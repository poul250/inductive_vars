#include <algorithm>
#include <vector>
#include <functional>
#include <unordered_set>
#include <unordered_map>
#include <iostream>

#define export exports // for c++ compatibility
extern "C" {
  #include "qbe/all.h"
}
#undef export


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
    result |= ((ref.type) << 28);
    return result;
  }
};

bool operator==(const Ref& lhs, const Ref& rhs) noexcept {
  return req(lhs, rhs);
}

struct Loop {
  Blk* head;
  std::unordered_set<Blk*> blocks;
  std::unordered_set<Ref, ref_hash> invariant_vars;

  template<typename THead, typename TBlocks>
  Loop(THead&& _head, TBlocks&& _blocks)
      : head(std::forward<THead>(_head))
      , blocks(std::forward<TBlocks>(_blocks)) {
  }

  bool operator==(const Loop& other) const noexcept {
    return head == other.head && blocks == other.blocks;
  }

  template<typename TFunc>
  void ForEachInstruction(const TFunc& func) {
    for (auto blk : blocks) {
      for (auto instr = blk->ins; instr < blk->ins + blk->nins; ++instr) {
        func(*blk, *instr);
      }
    }
  }

  std::unordered_set<uint> GetDeclarations() {
    std::unordered_set<uint> declarations;
    ForEachInstruction(
      [&declarations](const Blk& blk, const Ins& ins) {
        if (ins.to.type == RTmp) {
          declarations.insert(ins.to.val);
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
      return declarations.find(ref.val) == declarations.cend();
    };

    size_t last_invariants_size;
    do {
      last_invariants_size = invariant_vars.size();
      
      ForEachInstruction(
        [this, &declared_out, &is_invariant](const Blk& blk, const Ins& ins) {
          if (ins.to.type != RTmp) {
            return;
          }
          for (auto ref = ins.arg; ref < ins.arg + 2; ++ref) {
            if (declared_out(*ref)) {
              invariant_vars.insert(*ref);
            }
          }
          if (std::all_of(ins.arg, ins.arg + 2, is_invariant)) {
            invariant_vars.insert(ins.to);
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

  static constexpr bool IsBinaryOp(const Ins& ins) noexcept {
    return ins.to.type == RTmp;
  }

  std::unordered_set<Ref, ref_hash> FindOriginalInductiveVars() {
    std::unordered_set<Ref, ref_hash> candidates;
    std::unordered_set<Ref, ref_hash> not_inductive;

    auto is_add = [](const Ins& ins) {
      return ins.op == Oadd;
    };
    auto is_sub = [](const Ins& ins) {
      return ins.op == Osub;
    };

    ForEachInstruction(
      [this, &candidates, &not_inductive](const Blk& blk, const Ins& ins) {
        if (IsBinaryOp(ins)) {
          const auto& cand = ins.to;
          if ((req(cand, ins.arg[0]) && this->IsInvariant(ins.arg[1]) || 
              req(cand, ins.arg[1]) && this->IsInvariant(ins.arg[0])) &&
              not_inductive.find(cand) == not_inductive.cend()) {
            candidates.insert(cand);
          } else {
            candidates.erase(cand);
            not_inductive.insert(cand);
          }
        }
      }
    );
    return candidates;
  }

  void FindInductiveVars(Fn* fn) {
    std::unordered_map<Ref, std::tuple<Ref, std::string, std::string>, ref_hash> val_to_var;
  
    const auto& original_inductive_vars = FindOriginalInductiveVars();
    for (const auto& original : original_inductive_vars) {
      val_to_var.emplace(
        std::make_pair(original, std::make_tuple(original, "1", "0")));
    }

    for (const auto& [var, val] : val_to_var) {
      const auto& [i, a, b] = val;
      std::cout << fn->tmp[i.val].name << " " << a << " " << b << std::endl;
    }
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
  }

  for (const auto& loop : loops) {
    for (const auto& block : loop.blocks) {
      std::cout << block->name << " ";
    }
    std::cout << " | ";
    for (const auto& inv : loop.invariant_vars) {
      std::cout << fn->tmp[inv.val].name << " ";
    }
    std::cout << std::endl;
  }
}

static void readdat(Dat *dat) {
  (void) dat;
}

int main(int argc, char ** argv) {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
