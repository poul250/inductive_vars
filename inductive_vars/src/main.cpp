#include <algorithm>
#include <deque>
#include <functional>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define export exports // for c++ compatibility
extern "C" {
  #include "qbe/all.h"
}
#undef export

// defines are bad practice in c++, but for similarity with another defines
#define ismath(o) (Oadd <= (o) && (o) <= Ocuod)
#define iscopy(o) ((o) == Ocopy)
#define isarithm(o) (Oadd <= (o) && (o) <= Oshl)
#define iscmp(o) (Oceqw <= (o) && (o) <= Ocuod)

using Edge = std::pair<Blk*, Blk*>;
struct edge_hash {
  inline std::size_t operator()(const Edge& edge) const {
    std::hash<Blk*> hasher;
    return hasher(edge.first) + hasher(edge.second);
  }
};
using Edges = std::unordered_set<Edge, edge_hash>;

struct ref_hash {
  inline std::size_t operator()(const Ref& ref) const {
    std::size_t result = ref.val;
    result |= ((ref.type) << 29);
    return result;
  }
};

bool operator==(const Ref& lhs, const Ref& rhs) noexcept {
  return req(lhs, rhs);
}

std::string to_string(Fn* fn, Ref ref) {
  if (ref.type == RCon) {
    const auto& con = fn->con[ref.val];
    if (con.flt == 0) {
      return std::to_string(con.bits.i);
    } else if (con.flt == 1) {
      return std::to_string(con.bits.s);
    } else {
      return std::to_string(con.bits.d);
    }
  } else if (ref.type == RTmp) {
    return {fn->tmp[ref.val].name};
  }
  throw std::runtime_error("Unknown ref.type");
}

struct Loop {
  using val_t = std::tuple<Ref, std::string, std::string>;

  Blk* head;
  std::unordered_set<Blk*> blocks;
  std::unordered_set<Ref, ref_hash> invariant_vars;
  std::unordered_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash> inductive_families;

  template<class THead, class TBlocks>
  Loop(THead&& _head, TBlocks&& _blocks)
      : head(std::forward<THead>(_head))
      , blocks(std::forward<TBlocks>(_blocks)) {
  }

  bool operator==(const Loop& other) const noexcept {
    return head == other.head && blocks == other.blocks;
  }

  template<class TFunc>
  void ForEachInstruction(const TFunc& func) {
    for (auto blk : blocks) {
      for (auto instr = blk->ins; instr < blk->ins + blk->nins; ++instr) {
        func(*blk, *instr);
      }
    }
  }

  std::unordered_set<Ref, ref_hash> GetDeclarations() {
    std::unordered_set<Ref, ref_hash> declarations;
    ForEachInstruction(
      [&declarations](const Blk& blk, const Ins& ins) {
        if (isarithm(ins.op) || iscopy(ins.op) || iscmp) {
          declarations.insert(ins.to);
        }
      }
    );
    return declarations;
  }

  // TODO: use reaching definitions
  void FindInvariants(Tmp* tmp, int ntmp) {
    const auto& declarations = GetDeclarations();

    auto is_invariant = [this](Ref ref) {
      return this->IsInvariant(ref);
    };
    auto declared_out = [&declarations](Ref ref) -> bool {
      return declarations.find(ref) == declarations.cend();
    };

    size_t last_invariants_size;
    do {
      last_invariants_size = invariant_vars.size();
      
      ForEachInstruction(
        [this, &declared_out, &is_invariant](const Blk& blk, const Ins& ins) {
          if (!(iscopy(ins.op) || isarithm(ins.op) || iscmp(ins.op))) {
            return;
          }
          for (auto ref = ins.arg; ref < ins.arg + 2; ++ref) {
            if (ref->type == RTmp && declared_out(*ref)) {
              this->invariant_vars.insert(*ref);
            }
          }
          if (std::all_of(ins.arg, ins.arg + 2, is_invariant)) {
            this->invariant_vars.insert(ins.to);
          }
        }
      );
  
    } while (invariant_vars.size() != last_invariants_size);
  }

  bool IsInvariant(const Ref& ref) const {
    if (ref.type == RCon) {
      return true;
    }
    if (invariant_vars.find(ref) != invariant_vars.cend()) {
      return true;
    }
    return false;
  }

  bool IsBaseInductiveIns(const Ins& ins) {
    if (ins.op == Oadd) {
      return ((ins.to == ins.arg[0] && IsInvariant(ins.arg[1]) ||
              ins.to == ins.arg[1] && IsInvariant(ins.arg[0])));
    } else if (ins.op == Osub) {
      return (ins.to == ins.arg[0] && IsInvariant(ins.arg[1]));
    }
    return false;
  }

  bool IsDerivedIndactiveIns(
      const std::unordered_map<Ref, val_t, ref_hash> inductive_vars,
      const Ins& ins) {
    
    if (ins.op == Oadd || ins.op == Omul) {
      return (inductive_vars.find(ins.arg[0]) != inductive_vars.cend() && 
              IsInvariant(ins.arg[1]) || IsInvariant(ins.arg[0]) && 
              inductive_vars.find(ins.arg[1]) != inductive_vars.cend());
    } else if (ins.op == Osub) {
      return (inductive_vars.find(ins.arg[0]) != inductive_vars.cend() &&
              IsInvariant(ins.arg[1]));
    }
    return false;
  }

  std::unordered_set<Ref, ref_hash> FindBaseInductiveVars() {
    std::unordered_set<Ref, ref_hash> candidates;
    std::unordered_set<Ref, ref_hash> not_inductive;

    ForEachInstruction(
      [this, &candidates, &not_inductive](const Blk& blk, const Ins& ins) {
        if (ins.to.type == RTmp) {
          if (not_inductive.find(ins.to) == not_inductive.cend() && 
              candidates.find(ins.to) == candidates.cend() &&
              this->IsBaseInductiveIns(ins)) {
            candidates.insert(ins.to);
          } else {
            candidates.erase(ins.to);
            not_inductive.insert(ins.to);
          }
        }
      }
    );
    return candidates;
  }

  int CountDefinitions(const Ref& ref) {
    int result = 0;
    ForEachInstruction(
      [&ref, &result](const Blk&, const Ins& ins) {
        result += ((ismath(ins.op) || iscopy(ins.op)) && ins.to == ref);
      }
    );

    return result;
  }

  void AddVal(
      Fn* fn, 
      std::unordered_map<Ref, val_t, ref_hash>& inductives, 
      const Ins& ins) {
    int ind_var = inductives.find(ins.arg[0]) != inductives.cend();
    int inv_var = 1 - ind_var;
    
    const auto& [i, a, b] = inductives[ins.arg[ind_var]];
    const auto& inv_as_str = to_string(fn, ins.arg[inv_var]);

    if (ins.op == Oadd) {
      inductives[ins.to] = {i, a, "(" + b + ")+" + inv_as_str};
    } else if (ins.op == Osub) {
      inductives[ins.to] = {i, a, "(" + b + ")-" + inv_as_str};
    } else if (ins.op == Omul) {
      inductives[ins.to] = {i, "(" + a + ")*" + inv_as_str, 
                               "(" + b + ")*" + inv_as_str};
    }
  }
  
  std::unordered_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash>
  GetFamilies(const std::unordered_map<Ref, val_t, ref_hash>& inds) {
    std::unordered_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash> res;

    for (const auto& [var, val] : inds) {
      const auto& [i, a, b] = val;
      res[i].emplace_back(var, val);
    }
    return res;
  }

  void FindInductiveVars(Fn* fn) {
    std::unordered_map<Ref, val_t, ref_hash> var_to_val;
    std::unordered_set<Ref, ref_hash> not_inductive;

    const auto& base_inductive_vars = FindBaseInductiveVars();
    for (const auto& var : base_inductive_vars) {
      var_to_val[var] = {var, "1", "0"};
    }

    size_t last_var_to_val_size;
    do {
      last_var_to_val_size = var_to_val.size();
      ForEachInstruction(
        [this, fn, &var_to_val](const Blk&, const Ins& ins) {
          if (ismath(ins.op)) {
            if (var_to_val.find(ins.to) == var_to_val.cend() &&
                this->IsDerivedIndactiveIns(var_to_val, ins) &&
                this->CountDefinitions(ins.to) == 1) {
              // TODO: check also no other definitions between
              // (last frames in 6.4.3)
              this->AddVal(fn, var_to_val, ins);
            }
          }
        }
      );
    } while (var_to_val.size() != last_var_to_val_size);

    this->inductive_families = GetFamilies(var_to_val);
  }
};


Edges FindBackEdges(Blk *start) {
  Edges back_edges;
  for (Blk *blk = start; blk; blk = blk->link) {
    if (blk->s1 && dom(blk->s1, blk)) {
      back_edges.insert({blk, blk->s1});
    }
    if (blk->s2 && dom(blk->s2, blk)) {
      back_edges.insert({blk, blk->s2});
    }
  }

  return back_edges;
}

void ExtendWithLoopBlocks(std::unordered_set<Blk*>& blocks, Blk* cur_block) {
  if (blocks.find(cur_block) != blocks.cend()) {
    return;
  }

  blocks.insert(cur_block);
  for (int i = 0; i < cur_block->npred; ++i) {
    ExtendWithLoopBlocks(blocks, cur_block->pred[i]);
  }
}

Loop FindLoop(const Edge& back_edge) {
  const auto& [start_block, loop_head] = back_edge;
  std::unordered_set<Blk*> loop_blocks = {loop_head};

  ExtendWithLoopBlocks(loop_blocks, start_block);
  return {loop_head, std::move(loop_blocks)};
}

std::vector<Loop> FindLoops(Blk *start) {
  std::vector<Loop> result;
  const auto& back_edges = FindBackEdges(start);

  for (const auto& back_edge : back_edges) {
    auto&& loop = FindLoop(back_edge);
    result.emplace_back(std::move(loop));
  }

  // TODO: do something with same loops
  return result;
}


void LifehokkuDlyaSamuraev(Fn* fn) {
  // fill fields in blocks like idom
  fillrpo(fn);
  fillpreds(fn);
  filluse(fn);
  memopt(fn);
  filldom(fn);
}


static void readfn(Fn *fn) {
  LifehokkuDlyaSamuraev(fn);
  printfn(fn, stdout);

  auto loops = FindLoops(fn->start);

  for (auto& loop : loops) {
    loop.FindInvariants(fn->tmp, fn->ntmp);
    loop.FindInductiveVars(fn);
    std::cout << "blocks: ";
    for (const auto& block : loop.blocks) {
      std::cout << block->name << " ";
    }
    std::cout << "| invariant variables: ";
    for (const auto& inv : loop.invariant_vars) {
      std::cout << fn->tmp[inv.val].name << " ";
    }
    std::cout << std::endl;
    for (const auto& [ind, family] : loop.inductive_families) {
      std::cout << to_string(fn, ind) << ":" << std::endl;
      for (const auto& [name, val] : family) {
        const auto& [i, a, b] = val;
        std::cout << "\t" << to_string(fn, name) << " = " 
                  << "<" << to_string(fn, i) << ", " << a << ", " << b << ">" 
                  << std::endl;
      }
    }
  }
}

static void readdat(Dat *dat) {
  (void) dat;
}

int main(int argc, char ** argv) {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
