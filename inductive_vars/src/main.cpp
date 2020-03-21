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

void ExtendWithCycleBlocks(std::unordered_set<Blk*>& blocks, Blk* cur_block) {
    blocks.insert(cur_block);
    const auto& pred_blocks = cur_block->pred;
    for (int i = 0; i < cur_block->npred; ++i) {
        if (blocks.find(pred_blocks[i]) == blocks.cend()) {
            ExtendWithCycleBlocks(blocks, pred_blocks[i]);
        }
    }
}

std::unordered_set<Blk*> FindCycleBlocks(const Edge& back_edge) {
    const auto& [start_block, cycle_head] = back_edge;
    std::unordered_set<Blk*> blocks = {cycle_head};

    ExtendWithCycleBlocks(blocks, start_block);
    return blocks;
}

std::vector<std::unordered_set<Blk*>> FindCycles(Blk *start) {
    std::vector<std::unordered_set<Blk*>> result;
    const auto& back_edges = FindBackEdges(start);

    for (const auto& back_edge : back_edges) {
        auto&& blocks = FindCycleBlocks(back_edge);
        result.emplace_back(std::move(blocks));
    }

    return result;
}

static void readfn (Fn *fn) {
    printfn(fn, stdout);
    const auto& cycles = FindCycles(fn->start);
    for (const auto& cycle : cycles) {
        for (const auto& block : cycle) {
            std::cout << block->id << " ";
        }
        std::cout << std::endl;
    }
}

static void readdat (Dat *dat) {
    (void) dat;
}

int main (int argc, char ** argv) {
    parse(stdin, "<stdin>", readdat, readfn);
    freeall();
}
