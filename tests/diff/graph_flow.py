import random
import sys

rng = random.Random(20261126)
commands = ["new FlowGraph.init_0", "do FlowGraph.add_node 0", "do FlowGraph.add_node 0",
            "do FlowGraph.op_index 0 0", "do FlowGraph.max_flow 0 0 1"]
for k in range(1, 101):
    n = rng.randrange(2, 7)
    commands.append(f"new FlowGraph.init_int {n}")
    for _ in range(rng.randrange(13)):
        u, v, cap = rng.randrange(n), rng.randrange(n), rng.randrange(7)
        if k % 2 == 0:
            commands.append(f"do FlowGraph.add_edge_max_flow {k} {u} {v} {cap}")
        else:
            commands.append(f"do FlowGraph.add_edge_min_cost_flow {k} {u} {v} {cap} {rng.randrange(11)}")
    if k % 2 == 0:
        commands.append(f"do FlowGraph.max_flow {k} 0 {n - 1}")
    else:
        commands.append(f"do FlowGraph.min_cost_flow {k} 0 {n - 1} {rng.randrange(9)}")
        commands.append(f"do FlowGraph.min_cost_flow_slope {k} 0 {n - 1} {rng.randrange(9)}")
    commands.extend(f"do FlowGraph.op_index {k} {v}" for v in range(n))

edge_cost = (2**(31 if sys.argv[1:] == ["int"] else 63) - 1) >> 2
for i, weight in enumerate([edge_cost, edge_cost + 1, 2 * edge_cost], 101):
    commands.extend([f"new FlowGraph.init_int 3",
                     f"do FlowGraph.add_edge_min_cost_flow {i} 0 1 1 {weight}",
                     f"do FlowGraph.add_edge_min_cost_flow {i} 1 2 1 {-edge_cost}",
                     f"do FlowGraph.min_cost_flow {i} 0 2 1",
                     f"do FlowGraph.op_index {i} 0"])

print("\n".join(commands))
