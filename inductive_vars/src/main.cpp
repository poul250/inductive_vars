#include <algorithm>
#include <functional>
#include <iostream>
#include <numeric>
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

// c++20 feature, code it by nahds D;
template<class Key, class Value, class Hash = std::hash<Key>>
struct hash_map : public std::unordered_map<Key, Value, Hash> {
  bool contains(const Key& key) const {
    return this->find(key) != this->cend();
  }
};
template<class Key, class Hash = std::hash<Key>>
struct hash_set : public std::unordered_set<Key, Hash> {
  bool contains(const Key& key) const {
    return this->find(key) != this->cend();
  }
};

using Edge = std::pair<const Blk*, const Blk*>;
struct edge_hash {
  inline std::size_t operator()(const Edge& edge) const {
    std::hash<const Blk*> hasher;
    return hasher(edge.first) + hasher(edge.second);
  }
};
using Edges = hash_set<Edge, edge_hash>;

struct ref_hash {
  inline std::size_t operator()(Ref ref) const {
    std::size_t result = ref.val;
    result |= ((ref.type) << 29);
    return result;
  }
};
using val_t = std::tuple<Ref, std::string, std::string>;

bool operator==(Ref lhs, Ref rhs) noexcept {
  return req(lhs, rhs);
}

bool dom(const Blk* blk, const Blk* dom_this) {
  return dom(const_cast<Blk*>(blk), const_cast<Blk*>(dom_this));
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

struct ReachingDefinitions {
  using RefToBlocks = 
      hash_map<Ref, hash_set<const Blk*>, ref_hash>;
  hash_map<const Blk*, hash_set<Ref, ref_hash>> gen;
  hash_map<const Blk*, RefToBlocks> kill;
  hash_map<const Blk*, RefToBlocks> in;

  RefToBlocks GetNewIn(Blk* blk) {
    RefToBlocks new_in;
    for (Blk** pred = blk->pred; pred < blk->pred + blk->npred; ++pred) {
      const auto& pred_gen = gen[*pred];
      const auto& pred_kill = kill[*pred];
      const auto& pred_in = in[*pred];
      for (const auto& pred_gen_ref : pred_gen) {
        new_in[pred_gen_ref].insert(*pred);
      }
      for (const auto& [pred_in_ref, pred_in_blocks] : pred_in) {
        const auto& kill_ref_it = pred_kill.find(pred_in_ref);
        if(kill_ref_it == pred_kill.cend()) {
          new_in[pred_in_ref].insert(pred_in_blocks.cbegin(), 
                                     pred_in_blocks.cend());
        } else {
          for (const auto& pred_in_block : pred_in_blocks) {
            if (!kill_ref_it->second.contains(pred_in_block)) {
              new_in[pred_in_ref].insert(pred_in_block);
            }
          } 
        }
      }
    }

    return new_in;
  }

  void FindReachingDefinitions(Fn* fn) {
    hash_set<Blk*> blocks;
    for (Blk *blk = fn->start; blk; blk = blk->link) {
      blocks.insert(blk);
    }
    for (const Blk* blk : blocks) {
      hash_set<Ref, ref_hash> block_gens;
      for (uint i = 0; i < blk->nins; ++i) {
          if (blk->nins && Tmp0 <= blk->ins[i].to.val) {
              block_gens.insert(blk->ins[i].to);
          }
      }
      gen.emplace(blk, std::move(block_gens));
    }

    for (const auto& [blk, blk_gens] : gen) {
      RefToBlocks block_kills;
      for (const auto& [other_blk, other_blk_gens] : gen) {
        if (blk == other_blk) {
          continue;
        }
        for (const auto& blk_gen : blk_gens) {
          if (other_blk_gens.contains(blk_gen)) {
            block_kills[blk_gen].insert(other_blk);
          }
        }
      }
      kill.emplace(blk, std::move(block_kills));
    }

    bool change = true;
    while (change) {
      change = false;
      for (Blk *blk = fn->start; blk; blk = blk->link) {
        auto&& new_in = GetNewIn(blk);
        if (in[blk] != new_in) {
          in[blk] = std::move(new_in);
          change = true;
        }
      }
    }
  }
};

struct Loop {
  const Blk* head;
  hash_set<const Blk*> blocks;
  hash_set<const Ins*> invariant_statements;
  hash_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash> inductive_families;

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

  bool IsInvariantArg(ReachingDefinitions& rd, const Blk& blk, 
                          const Ins& instr, Ref ref) {
    if (ref.type == RCon) {
      return true;
    }

    const auto& reaching_blocks = rd.in[&blk][ref];

    // check that all reaching definitions are out of the loop
    bool all_definitions_out = std::all_of(
      reaching_blocks.cbegin(), reaching_blocks.cend(),
      [this](const auto& blk) { return !this->blocks.contains(blk); }
    );
    if (all_definitions_out) {
      return true;
    }

    // should have only one reaching definition and in the loop.
    // try to find invariant reaching definition in this block
    for (const Ins* ins = &instr - 1; ins != blk.ins - 1; --ins) {
      if (ins->to == ref) {
        return invariant_statements.contains(ins);
      }
    }

    if (reaching_blocks.size() > 1) {
      return false;
    }
    const auto& reaching_blk = *reaching_blocks.begin();

    for (const Ins* ins = reaching_blk->ins + reaching_blk->nins - 1; 
        ins != reaching_blk->ins - 1; --ins) {
      if (ins->to == ref) {
        return invariant_statements.contains(ins);
      }
    }
    return false;
  }

  hash_set<const Blk*> GetExitBlocks() {
    hash_set<const Blk*> result;
    for (const Blk* blk : blocks) {
      if (blk->s1 && !blocks.contains(blk->s1)) {
        result.insert(blk);
      } else if (blk->s2 && !blocks.contains(blk->s2)) {
        result.insert(blk);
      }
    }
    return result;
  }

  hash_map<const Ref, int, ref_hash> CountDefinitions() {
    hash_map<const Ref, int, ref_hash> result;
    ForEachInstruction([&result](const Blk&, const Ins& ins) {
      if (ins.to.type == RTmp) {
        ++result[ins.to];
      }
    });
    return result;
  }

  void FindInvariants(Fn* fn, ReachingDefinitions& rd) {
    size_t last_invariants_size;
    const auto& definitions = CountDefinitions();
    const auto& exit_blocks = GetExitBlocks();

    do {
      last_invariants_size = invariant_statements.size();
      
      for (const Blk* blk : blocks) {
        bool dom_exits = std::all_of(exit_blocks.begin(), exit_blocks.end(),
          [blk](const Blk* exit_blk) { return dom(blk, exit_blk); });
        if (!dom_exits) continue;
  
        for (const Ins* ins = blk->ins; ins != blk->ins + blk->nins; ++ins) {
          if (ins->to.type != RTmp || definitions.at(ins->to) != 1) continue;
  
          bool invatiant_args = std::all_of(
            ins->arg, ins->arg + 1 + !iscopy(ins->op),
            [this, &rd, &blk, &ins](Ref ref) {
              return IsInvariantArg(rd, *blk, *ins, ref);
            }
          );
          if (!invatiant_args) {
            continue;
          }
          invariant_statements.insert(ins);
        }
      }
  
    } while (invariant_statements.size() != last_invariants_size);
  }

  bool IsBaseInductiveIns(ReachingDefinitions& rd, const Blk& blk,
                          const Ins& ins) {
    if (ins.op == Oadd) {
      if (ins.to == ins.arg[0] && IsInvariantArg(rd, blk, ins, ins.arg[1]) ||
          ins.to == ins.arg[1] && IsInvariantArg(rd, blk, ins, ins.arg[0])) {
        return true;
      }
      return false;
    } else if (ins.op == Osub) {
      return (ins.to == ins.arg[0] && IsInvariantArg(rd, blk, ins, ins.arg[1]));
    }
    return false;
  }

  hash_set<Ref, ref_hash> FindBaseInductiveVars(
      ReachingDefinitions& rd) {
    hash_set<Ref, ref_hash> candidates;
    hash_set<Ref, ref_hash> not_base_inductive;

    ForEachInstruction(
      [this, &rd, &candidates, &not_base_inductive](const Blk& blk, const Ins& ins) {
        if (ins.to.type == RTmp) {
          if (!not_base_inductive.contains(ins.to) && 
              !candidates.contains(ins.to) &&
              this->IsBaseInductiveIns(rd, blk, ins)) {
            candidates.insert(ins.to);
          } else {
            candidates.erase(ins.to);
            not_base_inductive.insert(ins.to);
          }
        }
      }
    );
    return candidates;
  }


  val_t CreateVal(Fn* fn, const val_t& derived_from, int op, Ref inv) {
    const auto& [i, a, b] = derived_from;
    const auto& sinv = to_string(fn, inv);
    if (op == Oadd) {
      return {i, a, "(" + b + ")+" + sinv};
    } else if (op == Osub) {
      return {i, a, "(" + b + ")-" + sinv};
    } else if (op == Omul) {
      return {i, "(" + a + ")*" + sinv, "(" + b + ")*" + sinv};
    } else {
      throw std::runtime_error("CreateVal Error");
    }
  }
  
  hash_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash>
  GetFamilies(const hash_map<Ref, val_t, ref_hash>& inds) {
    hash_map<Ref, std::vector<std::pair<Ref, val_t>>, ref_hash> result;

    for (const auto& [var, val] : inds) {
      const auto& [i, a, b] = val;
      result[i].emplace_back(var, val);
    }
    return result;
  }

  void FindInductiveVars(Fn* fn, ReachingDefinitions& rd) {
    hash_map<Ref, val_t, ref_hash> inductives;
    hash_set<Ref, ref_hash> not_inductive;

    const auto& base_inductive_vars = FindBaseInductiveVars(rd);
    for (const auto& var : base_inductive_vars) {
      inductives[var] = {var, "1", "0"};
    }

    auto definitions_count = CountDefinitions();

    size_t last_inductives_size;
    do {
      last_inductives_size = inductives.size();
      
      ForEachInstruction(
        [this, fn, &rd, &definitions_count, &base_inductive_vars, &inductives, &not_inductive](
            const Blk& blk, const Ins& ins) {
          // don't check for already inductives;
          if (inductives.contains(ins.to) || not_inductive.contains(ins.to)) {
            return;
          }

          // should be only one definition and mul or add
          if (!(ins.op == Oadd || ins.op == Omul) || 
              definitions_count[ins.to] != 1) {
            not_inductive.insert(ins.to);
            return;
          }

          // find invariant operand and potentially inductive
          Ref inv = ins.arg[0], ind = ins.arg[1];
          if (!IsInvariantArg(rd, blk, ins, inv)) {
            std::swap(inv, ind);
          }
          if (!IsInvariantArg(rd, blk, ins, inv)) {
            not_inductive.insert(ins.to);
            return;
          }
          
          if (!inductives.contains(ind)) {
            return;
          }

          // try to find reaching definition in this block
          for (const Ins* i = &ins - 1; i != blk.ins - 1; --i) {
            if (i->to == ind) {
              inductives.emplace(ins.to, CreateVal(fn, inductives[ind], ins.op, inv));
              return;
            }
          }
          
          const auto& reaching_blocks = rd.in[&blk][ind];
          int in_loop = std::count_if(reaching_blocks.cbegin(), reaching_blocks.cend(), [this](const Blk* blk) {
            return this->blocks.contains(blk);
          });
          if (in_loop != 1) {
            not_inductive.insert(ins.to);
            return;
          }
          inductives.emplace(ins.to, CreateVal(fn, inductives[ind], ins.op, inv));
        }
      );
    } while (inductives.size() != last_inductives_size);

    this->inductive_families = GetFamilies(inductives);
  }
};

bool operator==(const val_t& lhs, const val_t& rhs) {
  return std::get<0>(lhs) == std::get<0>(rhs) &&
         std::get<1>(lhs) == std::get<1>(rhs) &&
         std::get<2>(lhs) == std::get<2>(rhs);
}

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

void ExtendWithLoopBlocks(hash_set<const Blk*>& blocks, 
                          const Blk* cur_block) {
  if (blocks.contains(cur_block)) {
    return;
  }

  blocks.insert(cur_block);
  for (int i = 0; i < cur_block->npred; ++i) {
    ExtendWithLoopBlocks(blocks, cur_block->pred[i]);
  }
}

Loop FindLoop(const Edge& back_edge) {
  const auto& [start_block, loop_head] = back_edge;
  hash_set<const Blk*> loop_blocks;
  loop_blocks.insert(loop_head);

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

  ReachingDefinitions rd;
  rd.FindReachingDefinitions(fn);

  auto loops = FindLoops(fn->start);

  for (auto& loop : loops) {
    loop.FindInvariants(fn, rd);
    loop.FindInductiveVars(fn, rd);
    std::cout << "blocks: ";
    for (const auto& block : loop.blocks) {
      std::cout << block->name << " ";
    }
    std::cout << "| invariant instructions: ";
    for (const auto& inv : loop.invariant_statements) {
      std::cout << fn->tmp[inv->to.val].name << " ";
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
