//! Conflict counterexamples from the LR item graph. Based on Isradisaikul and
//! Myers, "Finding Counterexamples from Parsing Conflicts" (PLDI 2015), §§4–5.

/// Two unresolved actions on the same lookahead in one parser state.
/// Each side identifies either its reduction rule or its shift destination.
pub const Conflict = struct {
    state: *State,
    token: *Symbol,
    rules: [2]?*Rule,
    shifts: [2]?*State,
};

/// Find and print witnesses for every recorded conflict. The graph is shared
/// across searches; each conflict's search and rendering storage is temporary.
pub fn explain(zyt: *const Zitron, out: *Writer, dim_comments: bool) !void {
    var arena = std.heap.ArenaAllocator.init(zyt.allocator);
    defer arena.deinit();
    const graph = try Graph.create(arena.allocator(), zyt.sorted, zyt.nterminal);
    for (zyt.conflicts.items, 1..) |conflict, number| {
        var scratch = std.heap.ArenaAllocator.init(zyt.allocator);
        defer scratch.deinit();
        const alloc = scratch.allocator();
        const choices = try graph.conflictItems(alloc, conflict);
        try printConflict(out, &graph, zyt.filename, conflict, number, choices);
        const result = try findCounterexample(alloc, &graph, zyt, conflict, choices);
        try printCounterexample(alloc, out, result, conflict, dim_comments);
    }
}

/// Records comment starts while buffering one derivation, then aligns them to
/// its rightmost comment column. Lines without comments do not affect alignment.
const Comments = struct {
    report: *std.Io.Writer.Allocating,
    allocator: Allocator,
    positions: List(Position) = .empty,
    column: usize = 0,

    /// A comment's byte offset in the buffer and its visible starting column.
    const Position = struct { offset: usize, column: usize };

    /// Record the current buffer end as the start of a comment.
    fn mark(comments: *Comments) OOM!void {
        const text = comments.report.written();
        const start = if (std.mem.lastIndexOfScalar(u8, text, '\n')) |i| i + 1 else 0;
        // Before a comment there are only ASCII nonterminal names, spaces,
        // and single-column tree glyphs, not arbitrary terminal spellings.
        const column = std.unicode.utf8CountCodepoints(text[start..]) catch unreachable;
        comments.column = @max(comments.column, column);
        try comments.positions.append(comments.allocator, .{ .offset = text.len, .column = column });
    }

    /// Emit the buffered tree with padded comments, optionally dimming only
    /// their text. Padding uses visible columns rather than UTF-8 byte counts.
    fn write(comments: Comments, out: *Writer, dim: bool) Writer.Error!void {
        const text = comments.report.written();
        var cursor: usize = 0;
        for (comments.positions.items) |position| {
            try out.writeAll(text[cursor..position.offset]);
            try out.splatByteAll(' ', comments.column - position.column);
            const end = position.offset + (std.mem.indexOfScalar(u8, text[position.offset..], '\n') orelse
                (text.len - position.offset));
            if (dim) try out.writeAll("\x1b[2m");
            try out.writeAll(text[position.offset..end]);
            if (dim) try out.writeAll("\x1b[22m");
            cursor = end;
        }
        try out.writeAll(text[cursor..]);
    }
};

/// Identifies one LR item: a production and dot position in a particular state.
/// The same production and dot can occur in several states with different context.
const LRItemKey = struct { state: *State, rule: *Rule, dot: u32 };

/// A symbol-labelled edge to another index in Graph.items. In a forward list
/// it advances the dot; in a reverse list it identifies the preceding item.
const SymbolEdge = struct {
    item: u32,
    symbol: *Symbol,

    /// Compare symbols and endpoint states, allowing different items in that state.
    fn matches(edge: SymbolEdge, other: SymbolEdge, graph: *const Graph) bool {
        return edge.symbol == other.symbol and graph.itemState(edge.item) == graph.itemState(other.item);
    }
};

/// Search adjacency for an existing Config, which owns the rule, dot, state,
/// and follow set. `next`/`prev` cross a grammar symbol; `children`/`parents`
/// enter or leave a nonterminal's productions without consuming a symbol.
/// Every adjacency target is an index in Graph.items, not a parser-state number.
const LRItem = struct {
    config: *Config,
    next: List(SymbolEdge) = .empty,
    prev: List(SymbolEdge) = .empty,
    children: List(u32) = .empty,
    parents: List(u32) = .empty,

    /// Whether the dot has reached the end of this item's production.
    fn isComplete(item: *const LRItem) bool {
        return item.config.dot == item.config.rp.rhs.len;
    }

    /// The symbol after the dot, or null for a completed production.
    fn nextSymbol(item: *const LRItem) ?*Symbol {
        const cf = item.config;
        if (cf.dot >= cf.rp.rhs.len) return null;
        return cf.rp.rhs[cf.dot];
    }
};

/// Temporary search index over Zitron's existing Configs, with one item per
/// (state, rule, dot). Dense item IDs support search stacks and visited keys;
/// adjacency lists support traversal in both directions without rescanning states.
///
/// Config's propagation links retain symbol transitions, even after action-table
/// compression, but include closure links only when the remaining RHS is nullable.
/// Counterexample search needs every closure edge and its reverse, so creation
/// indexes the existing transitions and adds closure adjacency from grammar rules.
///
/// Configs and grammar objects are borrowed. The caller's arena owns the item
/// array, lookup table, adjacency lists, and start-production root IDs.
const Graph = struct {
    nterminal: usize,
    items: []LRItem,
    index: std.AutoHashMapUnmanaged(LRItemKey, u32),
    roots: []const u32,

    /// Assign dense IDs to the states' Configs, then connect symbol transitions
    /// and nonterminal expansions. Requires states with FindLinks already applied.
    fn create(alloc: Allocator, states: []const *State, nterminal: usize) !Graph {
        var items: List(LRItem) = .empty;
        var index: std.AutoHashMapUnmanaged(LRItemKey, u32) = .empty;
        var roots: List(u32) = .empty;
        for (states) |state| {
            var current: ?*Config = state.cfp;
            while (current) |cf| : (current = cf.next) {
                const id: u32 = @intCast(items.items.len);
                try index.put(alloc, .{ .state = state, .rule = cf.rp, .dot = cf.dot }, id);
                try items.append(alloc, .{ .config = cf });
                if (state.statenum == 0 and cf.dot == 0 and cf.rp.lhsStart) try roots.append(alloc, id);
            }
        }
        for (items.items, 0..) |*item, i| {
            const cf = item.config;
            const symbol = item.nextSymbol() orelse continue;
            // Propagation links preserve original transitions even after compression.
            var link = cf.fplp;
            while (link) |p| : (link = p.next) {
                if (p.cfp.rp != cf.rp or p.cfp.dot != cf.dot + 1) continue;
                const dest = index.get(.{ .state = p.cfp.stp.?, .rule = cf.rp, .dot = cf.dot + 1 }).?;
                const symbols = if (symbol.type == .multiterminal) symbol.subsym else &[_]*Symbol{symbol};
                for (symbols) |sp| {
                    try item.next.append(alloc, .{ .item = dest, .symbol = sp });
                    try items.items[dest].prev.append(alloc, .{ .item = @intCast(i), .symbol = sp });
                }
            }
            if (symbol.type != .nonterminal) continue;
            var rule = symbol.rule;
            while (rule) |rp| : (rule = rp.nextlhs) {
                const child = index.get(.{ .state = cf.stp.?, .rule = rp, .dot = 0 }).?;
                try item.children.append(alloc, child);
                try items.items[child].parents.append(alloc, @intCast(i));
            }
        }
        return .{ .nterminal = nterminal, .items = items.items, .index = index, .roots = roots.items };
    }

    /// Look up the existing parser configuration represented by an item ID.
    fn config(graph: *const Graph, id: u32) *Config {
        return graph.items[id].config;
    }

    /// Look up the parser state containing an indexed item.
    fn itemState(graph: *const Graph, id: u32) *State {
        return graph.config(id).stp.?;
    }

    /// Find the item IDs witnessing each action. A reduction has one completed
    /// item; several productions can explain a shift to the same destination.
    fn conflictItems(graph: *const Graph, alloc: Allocator, conflict: Conflict) ![2][]const u32 {
        var choices: [2]List(u32) = .{ .empty, .empty };
        for (0..2) |side| {
            if (conflict.rules[side]) |rp| {
                try choices[side].append(
                    alloc,
                    graph.index.get(.{ .state = conflict.state, .rule = rp, .dot = @intCast(rp.rhs.len) }).?,
                );
            } else {
                var cf: ?*Config = conflict.state.cfp;
                while (cf) |item| : (cf = item.next) {
                    const id = graph.index.get(.{ .state = conflict.state, .rule = item.rp, .dot = item.dot }).?;
                    for (graph.items[id].next.items) |edge| {
                        if (edge.symbol == conflict.token and
                            graph.itemState(edge.item) == conflict.shifts[side])
                        {
                            try choices[side].append(alloc, id);
                            break;
                        }
                    }
                }
            }
        }
        return .{ choices[0].items, choices[1].items };
    }

    /// Breadth-first search from start productions to any target item, tracking
    /// a concrete lookahead through closure. Optional constraints require a target
    /// lookahead and an exact sequence of shifted symbols and destination states.
    /// Returns the reconstructed root-to-target path, or null if none qualifies.
    fn path(
        graph: *const Graph,
        alloc: Allocator,
        targets: []const u32,
        lookahead: ?u32,
        prefix_edges: ?[]const SymbolEdge,
    ) !?[]const PathNode {
        // A scalar lookahead is sufficient here: FIRST and propagation distribute
        // over union. Visiting (item, terminal) avoids exponential set combinations.
        var queue: List(PathNode) = .empty;
        var seen: std.AutoHashMapUnmanaged(PathKey, void) = .empty;
        for (graph.roots) |root| try addPath(
            alloc,
            &queue,
            &seen,
            .{ .key = .{ .item = root, .lookahead = 0, .position = 0 }, .parent = null },
        );
        var head: usize = 0;
        while (head < queue.items.len) : (head += 1) {
            const node = queue.items[head];
            if ((lookahead == null or node.key.lookahead == lookahead.?) and
                (prefix_edges == null or node.key.position == prefix_edges.?.len) and
                std.mem.indexOfScalar(u32, targets, node.key.item) != null)
            {
                var result: List(PathNode) = .empty;
                var cursor: ?usize = head;
                while (cursor) |n| {
                    try result.append(alloc, queue.items[n]);
                    cursor = queue.items[n].parent;
                }
                std.mem.reverse(PathNode, result.items);
                return result.items;
            }
            const item = graph.items[node.key.item];
            for (item.next.items) |edge| {
                if (prefix_edges) |p| {
                    if (node.key.position == p.len) continue;
                    const expected = p[node.key.position];
                    if (!edge.matches(expected, graph)) continue;
                }
                try addPath(alloc, &queue, &seen, .{
                    .key = .{
                        .item = edge.item,
                        .lookahead = node.key.lookahead,
                        .position = if (prefix_edges != null) node.key.position + 1 else 0,
                    },
                    .parent = head,
                    .symbol = edge.symbol,
                });
            }
            if (item.children.items.len != 0) {
                const lookaheads = try graph.follow(alloc, item.config, node.key.lookahead);
                for (item.children.items) |child| for (lookaheads, 0..) |allowed, token| {
                    if (allowed) try addPath(alloc, &queue, &seen, .{
                        .key = .{ .item = child, .lookahead = @intCast(token), .position = node.key.position },
                        .parent = head,
                    });
                };
            }
        }
        return null;
    }

    /// Compute FIRST of the suffix after the nonterminal at the dot, including
    /// the inherited lookahead when that suffix is nullable. These are the
    /// lookaheads available when entering the nonterminal's productions.
    fn follow(graph: *const Graph, alloc: Allocator, cf: *Config, inherited: u32) ![]bool {
        const result = try alloc.alloc(bool, graph.nterminal);
        @memset(result, false);
        for (cf.rp.rhs[cf.dot + 1 ..]) |sp| {
            switch (sp.type) {
                .terminal => result[sp.index] = true,
                .multiterminal => for (sp.subsym) |sub| {
                    result[sub.index] = true;
                },
                .nonterminal => for (sp.firstset[0..result.len], result) |b, *r| {
                    r.* = r.* or b;
                },
            }
            if (sp.type != .nonterminal or !sp.lambda) return result;
        }
        result[inherited] = true;
        return result;
    }

    /// Extract a path's symbol transitions, omitting closure steps, to constrain
    /// the competing action's path to the same consumed prefix and state sequence.
    fn prefix(alloc: Allocator, nodes: []const PathNode) ![]const SymbolEdge {
        var result: List(SymbolEdge) = .empty;
        for (nodes) |node| if (node.symbol) |sp| {
            try result.append(alloc, .{ .item = node.key.item, .symbol = sp });
        };
        return result.items;
    }

    /// Reconstruct a derivation around a path's final item, placing the conflict
    /// marker at its dot. Unexpanded symbols remain leaves for later completion.
    fn pathTree(graph: *const Graph, alloc: Allocator, nodes: []const PathNode) !*DerivationTree {
        const last = nodes[nodes.len - 1];
        var tree = try itemTree(alloc, graph.config(last.key.item), true);
        var i = nodes.len - 1;
        while (i > 0) : (i -= 1) {
            if (nodes[i].symbol) |sp| {
                const cf = graph.config(nodes[i].key.item);
                tree.children[cf.dot - 1] = try leaf(alloc, sp);
                continue;
            }
            const cf = graph.config(nodes[i - 1].key.item);
            const parent = try itemTree(alloc, cf, false);
            parent.children[cf.dot] = tree;
            tree = parent;
        }
        return tree;
    }
};

/// A visited BFS configuration: item ID, concrete lookahead, and the number of
/// transitions matched against an optional prefix constraint.
const PathKey = struct { item: u32, lookahead: u32, position: usize };

/// One BFS step. `parent` indexes the search queue for path reconstruction;
/// `symbol` labels an incoming transition, or is null for closure steps and roots.
const PathNode = struct { key: PathKey, parent: ?usize, symbol: ?*Symbol = null };

/// Search evidence, independent of rendering. Unifying cases share a marked
/// leaf sequence; other tree pairs share a prefix or expose separate contexts.
/// The remaining tags distinguish failures to find the required items or paths.
const Evidence = union(enum) {
    missing_items,
    no_reduce_path,
    no_other_path,
    unifying: [2]*DerivationTree,
    unifying_paths: [2]*DerivationTree,
    common_prefix: [2]*DerivationTree,
    separate_contexts: [2]*DerivationTree,
};

/// Why paired search fell back to independent paths: exhausted work or a bound
/// on search size. Neither outcome proves that the grammar is unambiguous.
const FallbackReason = enum { exhausted, limit };

/// The evidence to display and, when applicable, why fallback search was used.
const Counterexample = struct {
    evidence: Evidence,
    fallback_reason: ?FallbackReason = null,
};

/// Prefer a shared witness from paired search, using a reachable reduction path
/// to guide outward growth. If that search fails or reaches its bound, obtain
/// independent lookahead-sensitive examples rather than discarding the conflict.
fn findCounterexample(
    alloc: Allocator,
    graph: *const Graph,
    zyt: *const Zitron,
    conflict: Conflict,
    choices: [2][]const u32,
) !Counterexample {
    if (choices[0].len == 0 or choices[1].len == 0) return .{ .evidence = .missing_items };
    const reduce_side: usize = if (conflict.rules[1] != null) 1 else 0;
    const first = try graph.path(
        alloc,
        choices[reduce_side],
        if (conflict.rules[reduce_side] != null) conflict.token.index else null,
        null,
    );
    const preferred_states = try alloc.alloc(bool, zyt.nstate);
    @memset(preferred_states, false);
    if (first) |nodes| for (nodes) |node| {
        const state = graph.itemState(node.key.item);
        preferred_states[state.statenum] = true;
    };
    var search = Search.init(alloc, graph, conflict.token);
    search.preferred_states = preferred_states;
    for (choices[0]) |a| for (choices[1]) |b| {
        try search.seed(a, b);
    };
    if (try search.run()) |trees| {
        if (!try checkTrees(alloc, trees, conflict.token)) return error.InvalidCounterexample;
        return .{ .evidence = .{ .unifying = trees } };
    }
    return .{
        .evidence = try findPathExamples(alloc, graph, zyt, conflict, choices, first, reduce_side),
        .fallback_reason = if (search.limited) .limit else .exhausted,
    };
}

/// Find a competing path, preferring the first path's consumed prefix. Complete
/// both derivations through the lookahead, then classify their relationship.
fn findPathExamples(
    alloc: Allocator,
    graph: *const Graph,
    zyt: *const Zitron,
    conflict: Conflict,
    choices: [2][]const u32,
    first: ?[]const PathNode,
    reduce_side: usize,
) !Evidence {
    const nodes = first orelse return .no_reduce_path;
    const other = 1 - reduce_side;
    const lookahead = if (conflict.rules[other] != null) conflict.token.index else null;
    const prefix_edges = try Graph.prefix(alloc, nodes);
    const matching = try graph.path(alloc, choices[other], lookahead, prefix_edges);
    const second = matching orelse (try graph.path(alloc, choices[other], lookahead, null)) orelse return .no_other_path;
    var trees: [2]*DerivationTree = undefined;
    trees[reduce_side] = try graph.pathTree(alloc, nodes);
    trees[other] = try graph.pathTree(alloc, second);
    const completion = try LookaheadCompletion.create(alloc, zyt, conflict.token);
    for (trees) |tree| {
        var after = false;
        var found = false;
        try completion.finish(tree, &after, &found);
    }
    if (try checkTrees(alloc, trees, conflict.token)) return .{ .unifying_paths = trees };
    return if (matching != null) .{ .common_prefix = trees } else .{ .separate_contexts = trees };
}

/// Print the conflict header and the source productions witnessing each action.
fn printConflict(
    out: *Writer,
    graph: *const Graph,
    filename: []const u8,
    conflict: Conflict,
    number: usize,
    choices: [2][]const u32,
) !void {
    const kind = if (conflict.rules[0] == null and conflict.rules[1] == null)
        "shift/shift"
    else if (conflict.rules[0] != null and conflict.rules[1] != null)
        "reduce/reduce"
    else
        "shift/reduce";
    try out.print("\nConflict {d}: {s} in state {d} on ", .{ number, kind, conflict.state.statenum });
    try printSymbol(out, conflict.token);
    try out.writeByte('\n');
    for (choices, 0..) |items, side| for (items) |id| {
        const cf = graph.config(id);
        try out.print(
            "  {s} ({s}:{d}, rule {d}): ",
            .{
                if (conflict.rules[side] == null) "shift " else "reduce",
                filename,
                cf.rp.ruleline,
                cf.rp.iRule,
            },
        );
        try printItem(out, cf);
        try out.writeByte('\n');
    };
}

/// Render search status, example sequences, and derivations from an analysis
/// result. This performs no further search or classification.
fn printCounterexample(
    alloc: Allocator,
    out: *Writer,
    result: Counterexample,
    conflict: Conflict,
    dim_comments: bool,
) !void {
    if (result.fallback_reason) |reason| {
        try out.print("  {s}; showing lookahead-sensitive examples.\n", .{
            if (reason == .limit) "Search limit reached" else "No unifying counterexample found",
        });
    }
    switch (result.evidence) {
        .missing_items => try out.writeAll("  No item witness available.\n"),
        .no_reduce_path => try out.writeAll("  No reachable lookahead-sensitive path.\n"),
        .no_other_path => try out.writeAll("  No reachable path for the competing action.\n"),
        .unifying, .unifying_paths => |trees| {
            try out.writeAll(if (result.evidence == .unifying)
                "  Unifying counterexample: "
            else
                "  Unifying counterexample from lookahead paths: ");
            try trees[0].printLeaves(out);
            try out.writeByte('\n');
            try printDerivations(alloc, out, trees, conflict, dim_comments);
        },
        .common_prefix, .separate_contexts => |trees| {
            try out.writeAll(if (result.evidence == .common_prefix)
                "  Nonunifying counterexamples (common prefix):\n"
            else
                "  Separate contexts reaching the same LALR state:\n");
            for (trees, 0..) |tree, side| {
                try out.print("    {s}: ", .{if (conflict.rules[side] == null) "shift " else "reduce"});
                try tree.printLeaves(out);
                try out.writeByte('\n');
            }
            try printDerivations(alloc, out, trees, conflict, dim_comments);
        },
    }
}

/// Enqueue a BFS configuration only on its first visit, retaining that visit's
/// predecessor so the shortest graph path can be reconstructed.
fn addPath(
    alloc: Allocator,
    queue: *List(PathNode),
    seen: *std.AutoHashMapUnmanaged(PathKey, void),
    node: PathNode,
) !void {
    const entry = try seen.getOrPut(alloc, node.key);
    if (!entry.found_existing) try queue.append(alloc, node);
}

/// A partial grammar derivation. A rule-bearing node expands its LHS into
/// children; a symbol-only leaf is still opaque. A leaf with no symbol marks
/// the conflict position and consumes no grammar symbol.
const DerivationTree = struct {
    symbol: ?*Symbol,
    rule: ?*Rule = null,
    children: []*DerivationTree = &.{},

    /// Allocate the left-to-right leaf sequence, retaining null conflict markers.
    fn leaves(tree: *const DerivationTree, alloc: Allocator) OOM![]const ?*Symbol {
        var result: List(?*Symbol) = .empty;
        try tree.collect(alloc, &result);
        return result.items;
    }

    /// Append leaves recursively; expanded empty productions contribute nothing.
    fn collect(tree: *const DerivationTree, alloc: Allocator, result: *List(?*Symbol)) OOM!void {
        if (tree.rule != null) {
            for (tree.children) |child| try child.collect(alloc, result);
        } else try result.append(alloc, tree.symbol);
    }

    /// Check that each expansion matches its production, ignoring conflict
    /// markers and allowing a token-class member in place of the class symbol.
    fn valid(tree: *const DerivationTree) bool {
        const rp = tree.rule orelse return true;
        if (tree.symbol != rp.lhs) return false;
        var i: usize = 0;
        for (tree.children) |child| {
            const sp = child.symbol orelse continue;
            if (i == rp.rhs.len or !child.valid()) return false;
            const expected = rp.rhs[i];
            if (expected != sp and
                (expected.type != .multiterminal or
                    std.mem.indexOfScalar(*Symbol, expected.subsym, sp) == null)) return false;
            i += 1;
        }
        return i == rp.rhs.len;
    }

    /// Print the example sequence, showing the conflict marker as a bullet.
    fn printLeaves(tree: *const DerivationTree, out: *Writer) Writer.Error!void {
        if (tree.rule != null) {
            for (tree.children) |child| try child.printLeaves(out);
        } else if (tree.symbol) |sp| {
            try printSymbol(out, sp);
            try out.writeByte(' ');
        } else try out.writeAll("• ");
    }

    /// Render tree branches, source productions, explicit empty expansions, and
    /// the marked action. Record comment starts for the later alignment pass.
    fn print(
        tree: *const DerivationTree,
        out: *Writer,
        indent: ?*const Indent,
        action: []const u8,
        token: *Symbol,
        comments: *Comments,
    ) (Writer.Error || OOM)!void {
        try printTreePrefix(out, indent);
        if (tree.rule) |rp| {
            try out.print("{s}  ", .{rp.lhs.name});
            try comments.mark();
            try out.print("// L{d}   {s} ::=", .{ rp.ruleline, rp.lhs.name });
            for (rp.rhs) |sp| {
                try out.writeByte(' ');
                try printSymbol(out, sp);
            }
            if (rp.rhs.len == 0) try out.writeByte(' ');
            try out.writeAll(".\n");
            if (rp.rhs.len == 0) {
                const empty_indent: Indent = .{ .parent = indent, .last = tree.children.len == 0 };
                try printTreePrefix(out, &empty_indent);
                try out.writeAll("ε  ");
                try comments.mark();
                try out.writeAll("// empty: consumes no input\n");
            }
            for (tree.children, 0..) |child, i| {
                const child_indent: Indent = .{ .parent = indent, .last = i + 1 == tree.children.len };
                try child.print(out, &child_indent, action, token, comments);
            }
        } else if (tree.symbol) |sp| {
            try printSymbol(out, sp);
            try out.writeByte('\n');
        } else {
            try out.writeAll("•  ");
            try comments.mark();
            try out.print("// {s} here; lookahead: ", .{action});
            try printSymbol(out, token);
            if (token.index == 0) try out.writeAll(" (end of input)");
            try out.writeByte('\n');
        }
    }
};

/// An ancestor chain describing which tree columns still need vertical bars.
/// Each frame records whether its node is the last sibling at that depth.
const Indent = struct {
    parent: ?*const Indent,
    last: bool,

    /// Print ancestor continuation columns, without the current node's connector.
    fn print(indent: *const Indent, out: *Writer) Writer.Error!void {
        if (indent.parent) |parent| try parent.print(out);
        try out.writeAll(if (indent.last) "    " else "│   ");
    }
};

/// Print the base indentation, ancestor columns, and this node's branch connector.
fn printTreePrefix(out: *Writer, indent: ?*const Indent) Writer.Error!void {
    try out.writeAll("    ");
    if (indent) |node| {
        if (node.parent) |parent| try parent.print(out);
        try out.writeAll(if (node.last) "└── " else "├── ");
    }
}

/// Allocate an opaque symbol leaf, or a conflict marker when symbol is null.
fn leaf(alloc: Allocator, symbol: ?*Symbol) !*DerivationTree {
    const tree = try alloc.create(DerivationTree);
    tree.* = .{ .symbol = symbol };
    return tree;
}

/// Allocate a production expansion using the supplied child slice without copying it.
fn branch(alloc: Allocator, rule: *Rule, children: []*DerivationTree) !*DerivationTree {
    const tree = try alloc.create(DerivationTree);
    tree.* = .{ .symbol = rule.lhs, .rule = rule, .children = children };
    return tree;
}

/// Expand an item's production into opaque RHS leaves, optionally inserting a
/// conflict marker at the dot, including for an empty production.
fn itemTree(alloc: Allocator, cf: *Config, marked: bool) !*DerivationTree {
    const children = try alloc.alloc(*DerivationTree, cf.rp.rhs.len + @intFromBool(marked));
    var n: usize = 0;
    for (0..cf.rp.rhs.len + 1) |i| {
        if (marked and cf.dot == i) {
            children[n] = try leaf(alloc, null);
            n += 1;
        }
        if (i < cf.rp.rhs.len) {
            children[n] = try leaf(alloc, cf.rp.rhs[i]);
            n += 1;
        }
    }
    return branch(alloc, cf.rp, children);
}

/// Print a grammar symbol, restoring a literal's closing quote or listing a
/// token class's alternatives separated by vertical bars.
fn printSymbol(out: *Writer, sp: *Symbol) Writer.Error!void {
    if (sp.type == .multiterminal) {
        for (sp.subsym, 0..) |sub, i| {
            if (i != 0) try out.writeByte('|');
            try printSymbol(out, sub);
        }
    } else {
        try out.writeAll(sp.name);
        if (sp.name.len != 0 and sp.name[0] == '"') try out.writeByte('"');
    }
}

/// Print a production with a bullet at its LR dot position.
fn printItem(out: *Writer, cf: *Config) !void {
    try out.print("{s} ::=", .{cf.rp.lhs.name});
    for (0..cf.rp.rhs.len + 1) |i| {
        if (i == cf.dot) try out.writeAll(" •");
        if (i < cf.rp.rhs.len) {
            try out.writeByte(' ');
            try printSymbol(out, cf.rp.rhs[i]);
        }
    }
}

/// Label and print both action derivations, aligning comments independently
/// within each tree and applying the caller's terminal-dimming preference.
fn printDerivations(
    alloc: Allocator,
    out: *Writer,
    trees: [2]*DerivationTree,
    conflict: Conflict,
    dim_comments: bool,
) !void {
    const same_action = (conflict.rules[0] == null) == (conflict.rules[1] == null);
    for (trees, 0..) |tree, side| {
        const action = if (conflict.rules[side] == null) "shift" else "reduce";
        try out.writeAll("\n  ");
        if (same_action) try out.writeAll(if (side == 0) "First " else "Second ");
        const label = if (same_action) action else if (conflict.rules[side] == null) "Shift" else "Reduce";
        try out.print("{s} derivation:\n", .{label});
        var report: std.Io.Writer.Allocating = .init(alloc);
        defer report.deinit();
        var comments: Comments = .{ .report = &report, .allocator = alloc };
        try tree.print(&report.writer, null, action, conflict.token, &comments);
        try comments.write(out, dim_comments);
    }
}

/// Reject invalid productions, missing/duplicate markers, or a wrong lookahead.
/// For valid trees, return whether their complete marked leaf sequences match.
fn checkTrees(alloc: Allocator, trees: [2]*DerivationTree, token: *Symbol) !bool {
    var leaves: [2][]const ?*Symbol = undefined;
    for (trees, 0..) |tree, side| {
        if (!tree.valid()) return error.InvalidCounterexample;
        leaves[side] = try tree.leaves(alloc);
        var marker: ?usize = null;
        for (leaves[side], 0..) |sp, i| if (sp == null) {
            if (marker != null) return error.InvalidCounterexample;
            marker = i;
        };
        const next = (marker orelse return error.InvalidCounterexample) + 1;
        if (token.index == 0) {
            if (next != leaves[side].len) return error.InvalidCounterexample;
        } else if (next == leaves[side].len or leaves[side][next] != token) {
            return error.InvalidCounterexample;
        }
    }
    return std.mem.eql(?*Symbol, leaves[0], leaves[1]);
}

/// Per-symbol production choices for expanding to empty or exposing a requested
/// lookahead as the first terminal. Used to make fallback paths show concrete
/// input immediately after the conflict marker while leaving later symbols opaque.
const LookaheadCompletion = struct {
    alloc: Allocator,
    token: *Symbol,
    nullable: []?*Rule,
    leading: []?*Rule,
    positions: []usize,

    /// Relax production costs to a fixed point, retaining the cheapest nullable
    /// and token-leading expansions. Positive expansion costs avoid choosing
    /// recursive cycles; unreachable symbols retain null rule choices.
    fn create(alloc: Allocator, zyt: *const Zitron, token: *Symbol) !LookaheadCompletion {
        const count = zyt.symbols.len;
        const nullable = try alloc.alloc(?*Rule, count);
        const leading = try alloc.alloc(?*Rule, count);
        const positions = try alloc.alloc(usize, count);
        const empty_cost = try alloc.alloc(usize, count);
        const lead_cost = try alloc.alloc(usize, count);
        @memset(nullable, null);
        @memset(leading, null);
        @memset(empty_cost, INF);
        @memset(lead_cost, INF);
        var changed = true;
        while (changed) {
            changed = false;
            var rule: ?*Rule = zyt.rule;
            while (rule) |rp| : (rule = rp.next) {
                var cost: usize = 1;
                for (rp.rhs, 0..) |sp, i| {
                    const child_cost = switch (sp.type) {
                        .terminal => if (sp == token) @as(usize, 0) else INF,
                        .multiterminal => if (std.mem.indexOfScalar(*Symbol, sp.subsym, token) != null)
                            @as(usize, 0)
                        else
                            INF,
                        .nonterminal => lead_cost[sp.index],
                    };
                    const candidate = cost +| child_cost;
                    if (candidate < lead_cost[rp.lhs.index]) {
                        lead_cost[rp.lhs.index] = candidate;
                        leading[rp.lhs.index] = rp;
                        positions[rp.lhs.index] = i;
                        changed = true;
                    }
                    cost +|= if (sp.type == .nonterminal) empty_cost[sp.index] else INF;
                }
                if (cost < empty_cost[rp.lhs.index]) {
                    empty_cost[rp.lhs.index] = cost;
                    nullable[rp.lhs.index] = rp;
                    changed = true;
                }
            }
        }
        return .{
            .alloc = alloc,
            .token = token,
            .nullable = nullable,
            .leading = leading,
            .positions = positions,
        };
    }

    /// Build an empty derivation for a symbol known to have a nullable choice.
    fn emptyTree(completion: *const LookaheadCompletion, sp: *Symbol) OOM!*DerivationTree {
        const rp = completion.nullable[sp.index].?;
        const children = try completion.alloc.alloc(*DerivationTree, rp.rhs.len);
        for (rp.rhs, children) |child, *tree| tree.* = try completion.emptyTree(child);
        return branch(completion.alloc, rp, children);
    }

    /// Expose the requested terminal, expanding any preceding nullable symbols
    /// and leaving the suffix opaque. Requires a known token-leading choice.
    fn leadingTree(completion: *const LookaheadCompletion, sp: *Symbol) OOM!*DerivationTree {
        if (sp.type != .nonterminal) return leaf(completion.alloc, completion.token);
        const rp = completion.leading[sp.index].?;
        const pos = completion.positions[sp.index];
        const children = try completion.alloc.alloc(*DerivationTree, rp.rhs.len);
        for (rp.rhs, children, 0..) |child, *tree, i| {
            tree.* = if (i < pos)
                try completion.emptyTree(child)
            else if (i == pos)
                try completion.leadingTree(child)
            else
                try leaf(completion.alloc, child);
        }
        return branch(completion.alloc, rp, children);
    }

    /// Walk past the conflict marker, replacing nullable leaves with empty trees
    /// until the requested lookahead can be exposed. The flags carry traversal
    /// state across siblings; stop expanding once that terminal has been found.
    fn finish(
        completion: *const LookaheadCompletion,
        tree: *DerivationTree,
        after: *bool,
        found: *bool,
    ) OOM!void {
        if (found.*) return;
        if (tree.rule != null) {
            for (tree.children) |child| try completion.finish(child, after, found);
        } else if (tree.symbol) |sp| {
            if (!after.*) return;
            if (sp == completion.token or
                (sp.type == .nonterminal and completion.leading[sp.index] != null) or
                (sp.type == .multiterminal and
                    std.mem.indexOfScalar(*Symbol, sp.subsym, completion.token) != null))
            {
                tree.* = (try completion.leadingTree(sp)).*;
                found.* = true;
            } else if (sp.type == .nonterminal and completion.nullable[sp.index] != null) {
                tree.* = (try completion.emptyTree(sp)).*;
            }
        } else after.* = true;
    }
};

/// One side of paired search: an item-ID stack and the partial derivations of
/// its traversed symbols. They are not parallel arrays: closure adds an item
/// without a tree, and the conflict marker contributes a tree without a symbol.
const DerivationStack = struct {
    items: []const u32,
    trees: []*DerivationTree,

    /// Resolve the item at the stack's current parsing position.
    fn top(stack: *const DerivationStack, graph: *const Graph) *const LRItem {
        const id = stack.items[stack.items.len - 1];
        return &graph.items[id];
    }

    /// Resolve the earliest item whose left context may still need to grow.
    fn first(stack: *const DerivationStack, graph: *const Graph) *const LRItem {
        const id = stack.items[0];
        return &graph.items[id];
    }

    /// Return the completed production when it spans the entire item stack.
    fn rootRule(stack: *const DerivationStack, graph: *const Graph) ?*Rule {
        const item = stack.top(graph);
        if (!item.isComplete()) return null;
        const rule = item.config.rp;
        if (stack.items.len != rule.rhs.len + 1) return null;
        return rule;
    }

    /// Copy this stack with a symbol transition and its corresponding leaf appended.
    fn advance(stack: *const DerivationStack, alloc: Allocator, edge: SymbolEdge) !DerivationStack {
        const tree = try leaf(alloc, edge.symbol);
        return .{
            .items = try append(u32, alloc, stack.items, edge.item),
            .trees = try append(*DerivationTree, alloc, stack.trees, tree),
        };
    }

    /// Copy this stack with a predecessor symbol and its leaf prepended.
    fn precede(stack: *const DerivationStack, alloc: Allocator, edge: SymbolEdge) !DerivationStack {
        const tree = try leaf(alloc, edge.symbol);
        return .{
            .items = try prepend(u32, alloc, stack.items, edge.item),
            .trees = try prepend(*DerivationTree, alloc, stack.trees, tree),
        };
    }
};

/// Two partial derivations being grown toward the same marked leaf sequence.
/// `pending` constrains the next terminal after reductions; `shifted` records
/// progress past the initial marker. Cost and insertion order rank queued work.
const SearchPair = struct {
    stacks: [2]DerivationStack,
    pending: []const bool,
    shifted: bool = false,
    cost: usize = 0,
    serial: usize = 0,

    /// Return both complete root productions when they derive the same nonterminal.
    fn commonRoot(pair: *const SearchPair, graph: *const Graph) ?[2]*Rule {
        const left = pair.stacks[0].rootRule(graph) orelse return null;
        const right = pair.stacks[1].rootRule(graph) orelse return null;
        if (left.lhs != right.lhs) return null;
        return .{ left, right };
    }
};

/// Bounded priority search over paired derivations. It grows matching prefixes
/// backward through the item graph and advances both sides over matching symbols,
/// allowing independent expansions and reductions between those shared steps.
/// All queued stacks, trees, and visited keys live in the caller's scratch arena.
const Search = struct {
    alloc: Allocator,
    graph: *const Graph,
    token: *Symbol,
    queue: std.PriorityQueue(SearchPair, void, order),
    seen: std.StringHashMapUnmanaged(void) = .empty,
    serial: usize = 0,
    limited: bool = false,
    preferred_states: []const bool = &.{},

    const MAX_CONFIGURATIONS = 20000;
    const MAX_ITEMS = 128;

    /// Set up an empty search borrowing the graph; item pairs are seeded later.
    fn init(alloc: Allocator, graph: *const Graph, token: *Symbol) Search {
        return .{ .alloc = alloc, .graph = graph, .token = token, .queue = .empty };
    }

    /// Prefer lower heuristic cost, preserving insertion order when costs tie.
    fn order(_: void, a: SearchPair, b: SearchPair) std.math.Order {
        const priority = std.math.order(a.cost, b.cost);
        return if (priority == .eq) std.math.order(a.serial, b.serial) else priority;
    }

    /// Start at two competing items with a marker on each side and only the
    /// conflict terminal permitted as the next input token.
    fn seed(search: *Search, a: u32, b: u32) !void {
        const pending = try search.alloc.alloc(bool, search.graph.nterminal);
        @memset(pending, false);
        pending[search.token.index] = true;
        var pair: SearchPair = .{ .stacks = undefined, .pending = pending };
        for ([_]u32{ a, b }, 0..) |id, side| {
            pair.stacks[side] = .{
                .items = try search.alloc.dupe(u32, &.{id}),
                .trees = try search.alloc.dupe(*DerivationTree, &.{try leaf(search.alloc, null)}),
            };
        }
        try search.add(pair);
    }

    /// Enforce search bounds and queue an unseen pair of item stacks and input
    /// constraints. Trees and cost are excluded from the key, retaining the first
    /// witness reaching each configuration rather than every derivation of it.
    fn add(search: *Search, input: SearchPair) !void {
        if (search.serial >= MAX_CONFIGURATIONS or
            input.stacks[0].items.len > MAX_ITEMS or
            input.stacks[1].items.len > MAX_ITEMS)
        {
            search.limited = true;
            return;
        }
        var key: std.Io.Writer.Allocating = .init(search.alloc);
        for (input.stacks) |stack| {
            try key.writer.writeInt(usize, stack.items.len, .little);
            try key.writer.writeAll(std.mem.sliceAsBytes(stack.items));
        }
        for (input.pending) |allowed| try key.writer.writeByte(@intFromBool(allowed));
        try key.writer.writeByte(@intFromBool(input.shifted));
        const entry = try search.seen.getOrPut(search.alloc, key.written());
        if (entry.found_existing) return;
        var pair = input;
        pair.serial = search.serial;
        search.serial += 1;
        try search.queue.push(search.alloc, pair);
    }

    /// Explore queued pairs until both sides complete the same nonterminal and
    /// expose the conflict lookahead. Return their trees, or null on exhaustion
    /// or a search bound; `limited` distinguishes an incomplete bounded search.
    fn run(search: *Search) !?[2]*DerivationTree {
        var visited: usize = 0;
        while (search.queue.pop()) |pair| {
            visited += 1;
            if (visited > MAX_CONFIGURATIONS) {
                search.limited = true;
                return null;
            }
            const top = [2]*const LRItem{
                pair.stacks[0].top(search.graph),
                pair.stacks[1].top(search.graph),
            };
            const complete = [2]bool{ top[0].isComplete(), top[1].isComplete() };
            if (pair.commonRoot(search.graph)) |rules| {
                // If the conflict terminal has not been consumed, these local
                // derivations still need their enclosing right context.
                if (pair.shifted or search.token.index == 0) {
                    return .{
                        try branch(search.alloc, rules[0], pair.stacks[0].trees),
                        try branch(search.alloc, rules[1], pair.stacks[1].trees),
                    };
                }
            }
            for (0..2) |side| {
                if (complete[side]) {
                    const cf = top[side].config;
                    const length = cf.rp.rhs.len;
                    if (pair.stacks[side].items.len > length + 1) {
                        try search.reduce(pair, side, cf);
                    } else {
                        try search.prepare(pair, side, length);
                    }
                } else if (!complete[1 - side]) {
                    for (top[side].children.items) |child| {
                        var next = pair;
                        next.stacks[side].items = try append(u32, search.alloc, pair.stacks[side].items, child);
                        next.cost += 10;
                        try search.add(next);
                    }
                }
            }
            if (!complete[0] and !complete[1]) try search.transition(pair);
        }
        return null;
    }

    /// Reduce one completed production into its enclosing stack item, preserving
    /// the marker in its subtree and restricting pending input by its follow set.
    fn reduce(search: *Search, pair: SearchPair, side: usize, cf: *Config) !void {
        const stack = pair.stacks[side];
        const parent_pos = stack.items.len - cf.rp.rhs.len - 2;
        const parent_id = stack.items[parent_pos];
        const parent = &search.graph.items[parent_id];
        if (parent.nextSymbol() != cf.rp.lhs) return;
        const pending = try search.alloc.dupe(bool, pair.pending);
        var any = false;
        for (pending, cf.fws[0..pending.len]) |*p, allowed| {
            p.* = p.* and allowed;
            any = any or p.*;
        }
        if (!any) return;
        var begin = stack.trees.len;
        var count: usize = 0;
        while (count < cf.rp.rhs.len) {
            if (begin == 0) return;
            begin -= 1;
            if (stack.trees[begin].symbol != null) count += 1;
        }
        if (begin > 0 and stack.trees[begin - 1].symbol == null) begin -= 1;
        const tree = try branch(search.alloc, cf.rp, stack.trees[begin..]);
        for (parent.next.items) |edge| {
            if (edge.symbol != cf.rp.lhs) continue;
            var next = pair;
            next.pending = pending;
            next.stacks[side] = .{
                .items = try append(u32, search.alloc, stack.items[0 .. parent_pos + 1], edge.item),
                .trees = try append(*DerivationTree, search.alloc, stack.trees[0..begin], tree),
            };
            next.cost += 1;
            try search.add(next);
        }
    }

    /// Supply missing left context for a completed production: enter enclosing
    /// productions or prepend matching predecessor symbols to both sides.
    /// Penalize departures from the known reachable path to guide outward growth.
    fn prepare(search: *Search, pair: SearchPair, side: usize, length: usize) !void {
        const stack = pair.stacks[side];
        const first = stack.first(search.graph);
        if (stack.items.len == length + 1 and first.config.dot == 0) {
            for (first.parents.items) |parent| {
                if (!suffixAllows(search.graph.config(parent), pair.pending)) continue;
                var next = pair;
                next.stacks[side].items = try prepend(u32, search.alloc, stack.items, parent);
                next.cost += 10;
                try search.add(next);
            }
            return;
        }
        const other = 1 - side;
        const other_stack = pair.stacks[other];
        const other_first = other_stack.first(search.graph);
        if (other_first.config.dot == 0) {
            for (other_first.parents.items) |parent| {
                var next = pair;
                next.stacks[other].items = try prepend(u32, search.alloc, other_stack.items, parent);
                next.cost += 10;
                try search.add(next);
            }
        }
        for (first.prev.items) |a| for (other_first.prev.items) |b| {
            if (!a.matches(b, search.graph)) continue;
            var next = pair;
            next.stacks[side] = try stack.precede(search.alloc, a);
            next.stacks[other] = try other_stack.precede(search.alloc, b);
            next.cost += 2;
            if (!search.isPreferred(a.item)) next.cost += 100;
            try search.add(next);
        };
    }

    /// Whether an item stays on the preferred path, or no preference was supplied.
    fn isPreferred(search: *const Search, id: u32) bool {
        if (search.preferred_states.len == 0) return true;
        const state = search.graph.itemState(id);
        return search.preferred_states[state.statenum];
    }

    /// Check whether the suffix after the dot's nonterminal can begin with any
    /// pending terminal, consulting the enclosing follow set if it is nullable.
    fn suffixAllows(cf: *Config, pending: []const bool) bool {
        for (cf.rp.rhs[cf.dot + 1 ..]) |sp| {
            switch (sp.type) {
                .terminal => return pending[sp.index],
                .multiterminal => {
                    for (sp.subsym) |sub| if (pending[sub.index]) return true;
                    return false;
                },
                .nonterminal => {
                    for (sp.firstset[0..pending.len], pending) |starts, allowed| if (starts and allowed) return true;
                    if (!sp.lambda) return false;
                },
            }
        }
        for (cf.fws[0..pending.len], pending) |follows, allowed| if (follows and allowed) return true;
        return false;
    }

    /// Advance both derivations over the same symbol. Terminals must satisfy
    /// pending input constraints; an opaque nonterminal is allowed only when its
    /// FIRST set satisfies them and it cannot disappear through an empty expansion.
    fn transition(search: *Search, pair: SearchPair) !void {
        const a = pair.stacks[0].top(search.graph);
        const b = pair.stacks[1].top(search.graph);
        for (a.next.items) |ea| for (b.next.items) |eb| {
            if (ea.symbol != eb.symbol) continue;
            const sp = ea.symbol;
            if (sp.type == .terminal) {
                if (!pair.pending[sp.index]) continue;
            } else {
                // Keep nonterminals opaque only when every possible first token
                // respects reductions already taken. Nullable ones are expanded.
                if (!pair.shifted or sp.lambda) continue;
                var valid = true;
                for (sp.firstset[0..pair.pending.len], pair.pending) |starts, allowed| {
                    if (starts and !allowed) {
                        valid = false;
                        break;
                    }
                }
                if (!valid) continue;
            }
            var next = pair;
            for ([_]SymbolEdge{ ea, eb }, 0..) |edge, side| {
                next.stacks[side] = try pair.stacks[side].advance(search.alloc, edge);
            }
            const pending = try search.alloc.alloc(bool, pair.pending.len);
            @memset(pending, true);
            next.pending = pending;
            next.shifted = true;
            next.cost += 2;
            try search.add(next);
        };
    }
};

/// Copy a slice with one trailing value so queued search branches stay independent.
fn append(comptime T: type, alloc: Allocator, input: []const T, value: T) ![]T {
    const result = try alloc.alloc(T, input.len + 1);
    @memcpy(result[0..input.len], input);
    result[input.len] = value;
    return result;
}

/// Copy a slice with one leading value so outward growth preserves existing branches.
fn prepend(comptime T: type, alloc: Allocator, input: []const T, value: T) ![]T {
    const result = try alloc.alloc(T, input.len + 1);
    result[0] = value;
    @memcpy(result[1..], input);
    return result;
}

const INF = std.math.maxInt(usize);

const std = @import("std");
const Allocator = std.mem.Allocator;
const OOM = Allocator.Error;
const List = std.ArrayList;
const Writer = std.Io.Writer;

const z = @import("zitron.zig");
const Zitron = z.Zitron;
const Config = z.Config;
const State = z.State;
const Symbol = z.Symbol;
const Rule = z.Rule;
