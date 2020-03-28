#include <vector>
#include <unordered_set>
#include <stack>
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

struct Loop {
    Blk* head;
    std::unordered_set<Blk*> blocks;
    std::unordered_set<uint> invariants;

    template<typename THead, typename TBlocks>
    Loop(THead&& _head, TBlocks&& _blocks)
            : head(std::forward<THead>(_head))
            , blocks(std::forward<TBlocks>(_blocks)) {
    }

    bool operator==(const Loop& other) const noexcept {
        return head == other.head && blocks == other.blocks;
    }

    std::unordered_set<uint> GetDeclarations() {
        std::unordered_set<uint> declarations;
        for (auto block : blocks) {
            for (auto phi = block->phi; phi; phi = phi->link) {
                for (int i = 0; i < phi->narg; ++i) {
                    if (blocks.find(phi->blk[i]) != blocks.cend()) {
                        declarations.insert(phi->to.val);
                    }
                }
            }
            for (auto instr = block->ins; instr != block->ins + block->nins; ++instr) {
                if (instr->to.type == RTmp) {
                    declarations.insert(instr->to.val);
                }
            }
        }
        return declarations;
    }

    void FindInvariants(Tmp* tmp, int ntmp) {
        const auto& declarations = GetDeclarations();
        
        auto declared_out = [&declarations](Ref ref) -> bool {
            return declarations.find(ref.val) == declarations.cend();
        };

        bool updated = true;
        while (updated) {
            updated = false;
            for (auto block : blocks) {
                for (auto instr = block->ins; instr != block->ins + block->nins; ++instr) {
                    if (instr->to.type == RTmp && !IsInvariant(instr->to)) {
                        if (!IsInvariant(instr->arg[0]) && declared_out(instr->arg[0])) {
                            invariants.insert(instr->arg[0].val);
                            updated = true;
                        }
                        if (!IsInvariant(instr->arg[1]) && declared_out(instr->arg[1])) {
                            invariants.insert(instr->arg[1].val);
                            updated = true;
                        }
                        if (IsInvariant(instr->arg[0]) && IsInvariant(instr->arg[1])) {
                            invariants.insert(instr->to.val);
                            updated = true;
                        }
                    }
                }
            }
        }
    }

    bool IsInvariant(Ref ref) {
        if (ref.type == RCon) {
            return true;
        }
        if (invariants.find(ref.val) != invariants.cend()) {
            return true;
        }
        return false;
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


void lifehokku_dlya_samuraev(Fn* fn) {
    // fill fields in blocks like idom
    fillrpo(fn);
    fillpreds(fn);
    filluse(fn);
    memopt(fn);
    ssa(fn);
}


static void readfn(Fn *fn) {
    lifehokku_dlya_samuraev(fn);
    printfn(fn, stdout);
    auto loops = FindLoops(fn->start);
    for (auto& loop : loops) {
        loop.FindInvariants(fn->tmp, fn->ntmp);
    }

    for (const auto& loop : loops) {
        for (const auto& block : loop.blocks) {
            std::cout << block->id << " ";
        }
        std::cout << " | ";
        for (const auto& inv : loop.invariants) {
            std::cout << fn->tmp[inv].name << " ";
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
