//! Lemon: A LALR(1) Parser Generator, in Zig
//!
//! This file is a faithful translation of D. Richard Hipp's Lemon
//! parser into Zig.  The goal is to produce a binary which does
//! exactly what a lemon binary from lemon.c does, as such, this
//! program is for emitting C code, not Zig code.  This helps me
//! pressure test the port, because a correct program gives
//! identical outputs to the original.
//!
//! From there, the intention is to transform it into `zitron.zig`,
//! which will ultimately be a Zig code generator and use idiomatic
//! Zig (lemon.zig will be fairly C flavored by comparison).
//!

const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const ArrayHashMap = std.ArrayHashMapUnmanaged;
const MemoryPool = std.heap.MemoryPool;
const ArrayList = std.ArrayListUnmanaged;
const StringArrayHashMap = std.StringArrayHashMapUnmanaged;
const File = std.fs.File;

const OOM = Allocator.Error;

const isLower = std.ascii.isLower;
const isUpper = std.ascii.isUpper;
const isAlnum = std.ascii.isAlphanumeric;
const isAlpha = std.ascii.isAlphabetic;
const isSpace = std.ascii.isWhitespace;

const sort = std.mem.sort;

const assert = std.debug.assert;

const exit = std.process.exit;

const logger = std.log.scoped(.lemon);

const is_debug = builtin.mode == .Debug;

fn dbgassert(ok: bool) void {
    if (is_debug) {
        assert(ok);
    }
}

const dprint = std.debug.print;

//| NOTE: these should become build flags

const lemon_classic = true;
const do_not_optimize_terminals = true;
const print_aliases = false;

// Various print control variables

/// Prints which are already passing
const p_check1 = true;
/// Failing prints which I don't want to see
const p_check2 = false;
/// Prints I'm trying to get to pass
const p_check_this = false;
/// Possibly-useful prints which are ahead of the curve
const p_check_next = false;

const p_debug = false;

const p_print = false;
const p_errcnt = true;
const p_symbols = false;
const p_statefind = false;

// NOTE: This is not, in fact, how strcmp works.  If it turns out
// I need anything other than != 0 and == 0 from strcmp, which I doubt,
// I can decide how to handle that then.

fn strcmp(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

inline fn cast(T: type, val: anytype) T {
    return @as(T, @intCast(val));
}

// Definition of `int`.  This should help me figure out which should
// be unsigned, optional, or both, and which should in fact be an
// i32 (if any).  All type references to `int` should disappear.

const int = i32;

// Set low to exercise exception code
const MAXRHS = if (builtin.is_test) 5 else 1000;

threadlocal var showPrecendenceConflict: bool = false;

// Rules of thumb: Capitalize types, convert truthy ints to bool,
// and otherwise stick to the original types and names insofar as
// possible.  `char *` becomes `[]u8`, some of these can be const
// but it's not clear which.
//
// Some other changes are worth making on the fly, but they have to
// be mechanical enough that I can refer to the mutation automatically
// later when I have to use the thing.
//
// A lot of code which should be methods will get translated where it
// lays, as it were.  Moving that stuff inside the type containers will
// happen early though.

//| Line Notes: References to the original file will look like this:
//|
//| [1-20]

//| [1-193] These are forward declarations and custom string handling
//|   stuff, neither of which I expect to need.

//| [194-202] Options.  Here we start translating from C to Zig, both
//|   literally, and in terms of style.  Policy for enums: the type is
//|   PascalCased, the prefix (OPT_ in this case) is dropped, and the
//|   remainder is left alone.  This means often cramped C-isms, such
//|   as "dbl" below, but these are easy to refactor after the fact,
//|   and it's easier to use the same literal terms as the source code.

const OptionType = enum(u8) {
    flag = 1,
    int,
    dbl,
    str,
    fflag,
    fint,
    fdbl,
    fstr,
};

// Fortunately Zig has a mechanism for handling the fact that it has
// keywords which C lacks.  I will de-Magyar the code at some later
// point.

const S_Options = struct {
    type: OptionType,
    label: []const u8,
    arg: []u8,
    message: []const u8,
};

//| [203-238] More forward declarations

//| [239] This defines `LEMON_FALSE` and `LEMON_TRUE` as `Boolean`.  That,
//|   we can fairly skip.

//| [241-430] Fundamental data types

const SymbolType = enum {
    terminal,
    nonterminal,
    multiterminal,
};

const E_Assoc = enum {
    left,
    right,
    none,
    unk, // aka `unknown`
};

/// Symbols (terminals and nonterminals) of the grammar are stored in the following:
const Symbol = struct {
    /// Name of the symbol
    name: []const u8,
    /// Index number for this symbol
    index: u32,
    /// Symbols are all either terminal or nonterminal
    type: SymbolType = .terminal,
    /// Linked list of rules of this (if an NT)
    rule: ?*Rule,
    /// fallback token in case this token doesn't parse
    fallback: ?*Symbol,
    /// Precedence if defined (`null` otherwise)
    prec: ?u16 = null,
    /// Associativity if precedence is defined
    assoc: E_Assoc = .unk,
    /// First-set for all rules of this symbol
    firstset: []bool,
    /// True if NT and can generate an empty string
    lambda: bool,
    /// Number of times used
    usecnt: int,
    /// Code which executes whenever this symbol is
    /// popped from the stack during error processing
    destructor: []u8,
    /// Line number for start of destructor.  Set to
    /// -1 for duplicate destructors.
    destLineno: ?u32,
    /// The data type of information held by this
    /// object. Only used if type==NONTERMINAL
    datatype: []u8,
    /// The data type number.  In the parser, the value
    /// stack is a union.  The .yy%d element of this
    /// union is the correct data type for this object.
    dtnum: int, // No idea what the above means yet ¯\_(ツ)_/¯
    /// True if this symbol ever carries content - if
    /// it is ever more than just syntax
    bContent: bool,
    // following fields are used by MULTITERMINALs only

    /// Number of constituent symbols in the MULTI
    nsubsym: usize, // TODO: Probably redundant with this slice:
    //
    /// Array (slice) of constituent symbols
    subsym: []*Symbol,

    pub const empty: Symbol = .{
        .name = "UNIN!TIALIZED",
        .index = 0,
        .type = .nonterminal,
        .rule = null,
        .fallback = null,
        .prec = null,
        .assoc = .unk,
        .lambda = false,
        .firstset = undefined,
        .usecnt = 0,
        .destructor = undefined,
        .destLineno = null,
        .datatype = undefined,
        .dtnum = 0,
        .bContent = false,
        .nsubsym = 0,
        .subsym = undefined,
    };

    // Valid, if dodgy, mutable Symbol pointer target:
    pub var start: Symbol = start: {
        var starter: Symbol = .empty;
        starter.name = "!!!Invalid";
        break :start starter;
    };

    pub fn create(allocator: Allocator, name: []const u8) !*Symbol {
        const sp = try allocator.create(Symbol);
        errdefer allocator.destroy(sp);
        sp.* = .empty;
        //| [5446]
        sp.name = name;
        dbgassert(sp.name.len > 0);
        if (isUpper(name[0])) {
            sp.type = .terminal;
        }
        // These do return a pointer, conceivably that can fail?
        sp.firstset = try allocator.alloc(bool, 0);
        errdefer allocator.free(sp.firstset);
        sp.destructor = try allocator.alloc(u8, 0);
        errdefer allocator.free(sp.destructor);
        sp.datatype = try allocator.alloc(u8, 0);
        errdefer allocator.free(sp.datatype);
        sp.subsym = try allocator.alloc(*Symbol, 0);
        errdefer allocator.free(sp.subsym);
        return sp;
    }

    pub fn destroy(sp: *Symbol, allocator: Allocator) void {
        allocator.free(sp.firstset);
        allocator.free(sp.destructor);
        allocator.free(sp.datatype);
        allocator.free(sp.subsym);
        allocator.destroy(sp);
    }
};

/// Each production rule in the grammar is stored in the following structure.
const Rule = struct {
    /// Left-hand side of the rule
    lhs: *Symbol,
    /// Alias for the LHS (empty if none)
    lhsalias: []const u8,
    /// True if left-hand side is the start symbol
    lhsStart: bool,
    /// Line number for the rule
    ruleline: usize,
    /// The RHS symbols
    rhs: []*Symbol,
    /// Number of RHS symbols
    nrhs: usize, // NOTE: This should use rule.rhs.len, eventually.

    /// An alias for each RHS symbol (empty if none)
    rhsalias: [][]const u8,
    /// Line number at which code begins
    line: usize,
    /// The code executed when this rule is reduced
    code: []const u8,
    /// Setup code before code[] above
    codePrefix: []const u8,
    /// Breakdown code after code[] above
    codeSuffix: []const u8,
    /// Precedence symbol for this rule
    precsym: ?*Symbol,
    /// An index number for this rule
    index: u32,
    /// Rule number as used in the generated tables
    iRule: u32,
    /// True if this rule has no associated C code
    noCode: bool,
    /// True if the code has been emitted already
    codeEmitted: bool,
    /// True if this rule is ever reduced
    canReduce: bool,
    /// Reduce actions occur after optimization
    doesReduce: bool,
    /// Reduce is theoretically possible, but prevented
    /// by actions or other outside implementation
    neverReduce: bool,
    /// Next rule with the same LHS
    nextlhs: ?*Rule,
    /// Next rule in the global list
    next: ?*Rule,

    pub const empty = std.mem.zeroInit(Rule, .{ .lhs = undefined });

    pub fn create(allocator: Allocator) !*Rule {
        const rp = try allocator.create(Rule);
        rp.* = .empty;
        return rp;
    }

    pub fn destroy(rp: *Rule, allocator: Allocator) void {
        allocator.free(rp.rhs);
        allocator.free(rp.rhsalias);
        allocator.destroy(rp);
    }
};

const ConfigStatus = enum {
    complete,
    incomplete,
};

// A configuration is a production rule of the grammar together with
// a mark (dot) showing how much of that rule has been processed so far.
// Configurations also contain a follow-set which is a list of terminal
// symbols which are allowed to immediately follow the end of the rule.
// Every configuration is recorded as an instance of the following:

const Config = struct {
    /// The rule upon which the configuration is based
    rp: *Rule,
    /// The parse point
    dot: u32,
    /// Follow-set for this configuration only
    fws: []bool,
    /// Follow-set forward propagation links
    fplp: ?*PLink,
    /// Follow-set backwards propagation links
    bplp: ?*PLink,
    /// Pointer to state which contains this
    stp: ?*State,
    /// used during followset and shift computations
    status: ConfigStatus,
    /// Next configuration in the state
    next: ?*Config,
    /// The next basis configuration
    bp: ?*Config,

    pub const empty: Config = .{
        .rp = undefined,
        .dot = 0,
        .fws = &.{},
        .fplp = null,
        .bplp = null,
        .stp = null, // ??
        .status = .incomplete,
        .next = null,
        .bp = null,
    };
};

const E_Action = enum(u4) {
    shift,
    accept,
    reduce,
    @"error",
    /// A shift/shift conflict
    ssconflict,
    /// Was a reduce, but part of a conflict
    srconflict,
    /// Was a reduce, but part of a conflict
    rrconflict,
    /// Was a shift.  Precedence resolved conflict
    sh_resolved,
    /// Was reduce.  Precedence resolved conflict
    rd_resolved,
    /// Deleted by compression
    not_used,
    /// Shift first, then reduce
    shiftreduce,
    /// Was not initialized (sanity check)
    _not_initialized,
};

/// NOTE: This union is deduc'ed from the code at [3380]
/// It is not currently in use, but it would be a good idea
/// to go back later and make `action.x` into a tagged union,
/// instead of a bare union with a separated type tag.  Too
/// much deviation from the source for now.
const ActUnion = union(E_Action) {
    shift: *State,
    accept,
    reduce: *Rule,
    @"error",
    ssconflict: *State,
    srconflict: *Rule,
    rrconflict: *Rule,
    sh_resolved: *State,
    rd_resolved: *Rule,
    not_used,
    shiftreduce: *Rule,
    _not_initialized,
};

const ActionAllocator = MemoryPool(Action);
threadlocal var action_allocator: ActionAllocator = undefined; // init in main
threadlocal var action_age: usize = 0;

/// Every shift or reduce operation is stored as one of the following
const Action = struct {
    /// The look-ahead symbol
    sp: *Symbol = undefined,
    type: E_Action = ._not_initialized,
    x: union {
        stp: *State,
        rp: ?*Rule,
    } = undefined,
    /// SHIFTREDUCE optimization to this symbol
    spOpt: ?*Symbol = null,
    /// Next action for this state
    next: ?*Action = null,
    /// Next action with the same hash
    collide: ?*Action = null,
    /// Tie-breaker in sorting
    age: usize,

    // [490]
    pub fn new() !*Action {
        const act = try action_allocator.create();
        act.* = .{ .age = action_age };
        action_age += 1;
        return act;
    }

    //| NOTE: these two were originally one method, but I'm not in the mood to do
    //| the casting and other paperwork to get Zig to cooperate with that.  All of
    //| this code should get refactored later to change how that all works, but
    //| I'm out of budget to make on-the-fly changes as I get to the hairiest part
    //| of the original.

    pub fn addState(app: *?*Action, e_type: E_Action, sp: *Symbol, stp: *State) !void {
        const newaction = try Action.new();
        newaction.next = app.*;
        app.* = newaction;
        newaction.type = e_type;
        newaction.sp = sp;
        // newaction.spOpt = null;
        newaction.x = .{ .stp = stp };
    }

    pub fn addRule(app: *?*Action, e_type: E_Action, sp: *Symbol, rp: ?*Rule) !void {
        const newaction = try Action.new();
        newaction.next = app.*;
        app.* = newaction;
        newaction.type = e_type;
        newaction.sp = sp;
        // newaction.spOpt = null;
        newaction.x = .{ .rp = rp };
    }

    pub const sort = mergeSortFn(Action, "next", actioncmp);

    // Compare two actions.  Return `true` if the first is less than
    // or equal to the second, `false` otherwise.
    fn actioncmp(ap1: *Action, ap2: *Action) bool {
        if (ap1.sp.index < ap2.sp.index) return true;
        if (ap1.sp.index > ap2.sp.index) return false;
        if (@intFromEnum(ap1.type) < @intFromEnum(ap2.type)) return true;
        if (@intFromEnum(ap1.type) > @intFromEnum(ap2.type)) return false;
        // ap2 will cast identically because they have the same type:
        if (ap1.type == .reduce or ap1.type == .shiftreduce) {
            if (p_debug) dprint("ap1.type {s} ap2.type {s}\n", .{ @tagName(ap1.type), @tagName(ap2.type) });
            if (ap1.x.rp.?.index < ap2.x.rp.?.index) return true;
            if (ap1.x.rp.?.index > ap2.x.rp.?.index) return false;
        }
        {
            // otherwise... raw pointer comparison??
            // Let's see if this ever needs to happen:
            dprint("action sort: raw pointer comparison is reachable\n", .{});
            // .. and then not do it.
            return ap1.age <= ap2.age; // Equal is impossible but ¯\_(ツ)_/¯
            // This is the order they're subtracted in the original:
            //if (@intFromPtr(ap2) > @intFromPtr(ap1)) return false;
        }
    }
};

/// Each state of the generated parser's finite state machine
/// is encoded as an instance of the following structure.
const State = struct {
    /// The basis configurations for this state
    bp: ?*Config = null,
    /// All configurations in this set
    cfp: *Config = undefined,
    /// Sequential number for this state
    statenum: u32,
    /// List of actions for this state
    ap: ?*Action,
    /// Number of actions on terminals
    nTknAct: u32,
    /// Number of actions on nonterminals
    nNtAct: u32,
    /// yy_action[] offset for terminals
    iTnkOfst: ?u31,
    /// yy_action[] offset for nonterminals
    iNtOfst: ?u31,
    /// Default action is to REDUCE by this rule
    iDfltReduce: int, // Another ?u32 I think
    /// The default REDUCE rule.
    pDefltReduce: ?*Rule,
    /// True if this is an auto-reduce state
    autoreduce: bool,

    pub const empty: State = .{
        .statenum = 0,
        .ap = null,
        .nTknAct = 0,
        .nNtAct = 0,
        .iTnkOfst = null,
        .iNtOfst = null,
        .iDfltReduce = -1,
        .pDefltReduce = null,
        .autoreduce = false,
    };

    // [541]
    pub fn addAction(st: *State, sym: *Symbol, act_u: ActUnion) void {
        var newaction = Action.new();
        newaction.next = st.ap;
        st.ap = newaction;
        newaction.sp = sym;
        newaction.spOpt = null;
        newaction.x = act_u;
    }
};

const StateContext = struct {
    pub fn hash(_: StateContext, cfp: *Config) u32 {
        var h: u32 = 0;
        var next_cfg: ?*Config = cfp;
        while (next_cfg) |a| {
            h = h *% 571 +% a.rp.index *% 37 +% a.dot;
            next_cfg = a.bp;
        }
        return h;
    }

    pub fn eql(_: StateContext, a_cfg: *Config, b_cfg: *Config, _: usize) bool {
        var rc: i32 = 0;
        var a: ?*Config = a_cfg;
        var b: ?*Config = b_cfg;
        while (rc == 0 and a != null and b != null) {
            const a1: *Config = a.?;
            const b1: *Config = b.?;
            rc = cast(i32, a1.rp.index) - cast(i32, b1.rp.index);
            if (rc == 0) rc = cast(i32, a1.dot) - cast(i32, b1.dot);
            a = a1.bp;
            b = b1.bp;
        }
        if (rc == 0) {
            if (a) |_| rc = 1;
            if (b) |_| rc = -1;
        }
        return (rc == 0);
    }
};

//| [5681] State map stuff.

const StateSafe = struct {
    allocator: Allocator,
    safe: ArrayHashMap(*Config, *State, StateContext, true),
};

threadlocal var state_map: StateSafe = undefined;
threadlocal var is_state_map = false;

fn State_init(allocator: Allocator) !void {
    if (is_state_map) return;
    defer is_state_map = true;
    state_map.allocator = allocator;
    state_map.safe = .empty;
    try state_map.safe.ensureTotalCapacity(allocator, 128);
}

fn State_new() !*State {
    const sp = try state_map.allocator.create(State);
    sp.* = .empty;
    return sp;
}

fn State_find(bp: *Config) ?*State {
    dbgassert(is_state_map);
    if (p_statefind) {
        dprint("Looking for {s}:{d}-{d}\n", .{ bp.rp.lhs.name, bp.rp.index, bp.dot });
    }
    const maybe_sp = state_map.safe.get(bp);
    if (maybe_sp) |_| {
        if (p_statefind) dprint("  Found\n", .{});
    } else {
        if (p_statefind) dprint("  Not found\n", .{});
    }
    return maybe_sp;
}

fn State_insert(data: *State, key: *Config) !bool {
    dbgassert(is_state_map);
    if (p_statefind) dprint("Inserting {s}:{d}-{d}\n", .{ key.rp.lhs.name, key.rp.index, key.dot });
    if (state_map.safe.getKey(key)) |_| return false;
    if (p_statefind) dprint("  Inserted\n", .{});
    try state_map.safe.put(state_map.allocator, key, data);
    return true;
}

//| NOTE: These will be sorted, which invalidates the, uh, state,
//| of the state_map.  I think that's ok though.  Tracking what
//| of this data belongs to whom'st will be interesting.
//|

fn State_arrayof() []*State {
    return state_map.safe.values();
}

fn State_free() void {
    for (state_map.safe.values()) |stp| {
        Configlist_eat(stp.cfp, state_map.allocator);
        Configlist_eat(stp.bp, state_map.allocator);
    }
    state_map.safe.deinit(state_map.allocator);
}

/// A followset propagation link indicates that the contents of one
/// configuration followset should be propagated to another whenever
/// the first changes.
const PLink = struct {
    /// The configuration to which linked
    cfp: *Config,
    /// The next propagate link
    next: ?*PLink,
};

threadlocal var plink_freelist: MemoryPool(PLink) = undefined;
threadlocal var is_plink_freelist = false;

fn Plink_new() !*PLink {
    dbgassert(is_plink_freelist);
    return try plink_freelist.create();
}

/// Add a plink to a plink list
fn Plink_add(plink: *?*PLink, cfp: *Config) !void {
    const newlink = try Plink_new();
    newlink.cfp = cfp;
    newlink.next = plink.*;
    plink.* = newlink;
}

/// Transfer every plink on the list "from" to the list "to"
fn Plink_copy(to: *?*PLink, from_in: ?*PLink) void {
    var from: ?*PLink = from_in;
    var nextpl: ?*PLink = null;
    while (from) |this_pl| {
        nextpl = this_pl.next;
        this_pl.next = to.*;
        to.* = this_pl;
        from = nextpl;
    }
}

/// Delete every plink on the list
fn Plink_delete(plp_delete: ?*PLink) void {
    var this_plp: ?*PLink = plp_delete;
    while (this_plp) |plp| {
        const plp_next = plp.next;
        plink_freelist.destroy(plp);
        this_plp = plp_next;
    }
}

// /*********************** From the file "report.c" **************************/
// /*
// ** Procedures for generating reports and tables in the LEMON parser generator.
// */

/// Generate a filename with the given suffix.  Space to hold the
/// name comes from malloc() and must be freed by the calling
/// function.
fn file_makename(lemp: *Lemon, suffix: []const u8, output_dir: ?[]const u8) OOM![]u8 {
    var buf = ArrayList(u8){};
    errdefer buf.deinit(lemp.allocator);

    var w = buf.writer(lemp.allocator);
    var filename = lemp.filename;

    if (output_dir) |dir| {
        if (std.mem.lastIndexOfScalar(u8, filename, '/')) |i| {
            filename = filename[i + 1 ..];
        }
        try w.print("{s}/", .{dir});
    }

    if (std.mem.lastIndexOfScalar(u8, filename, '.')) |dot| {
        filename = filename[0..dot];
    }

    try w.print("{s}{s}", .{ filename, suffix });

    return try buf.toOwnedSlice(lemp.allocator);
}

/// Open a file with a name based on the name of the input file,
/// but with a different (specified) suffix, and return a pointer
/// to the stream.
fn file_open(lemp: *Lemon, suffix: []const u8, mode: File.CreateFlags) OOM!?File {
    if (lemp.outname.len > 0) lemp.allocator.free(lemp.outname);
    lemp.outname = try file_makename(lemp, suffix, null); // TODO: decide how to handle outputDir
    const fh = std.fs.cwd().createFile(lemp.outname, mode) catch |err| {
        lemp.errorcnt += 1;
        switch (err) {
            error.IsDir => {
                logger.err("file open error: path is a directory '{s}'", .{lemp.outname});
                return null;
            },
            error.FileNotFound => {
                logger.err("file open error: file not found '{s}'", .{lemp.outname});
                return null;
            },
            error.AccessDenied => {
                logger.err("file open error: permission denied '{s}'", .{lemp.outname});
                return null;
            },
            else => |e| {
                logger.err("file open error: unexpected error {s} opening '{s}'", .{ @errorName(e), lemp.outname });
                return null;
            },
        }
    };
    return fh;
}

/// Print the text of a rule
fn rule_print(writer: anytype, rp: *Rule) !void {
    try writer.print("{s}", .{rp.lhs.name});
    if (comptime print_aliases) {
        if (rp.lhsalias.len > 0) try writer.print("({s})", .{rp.lhsalias});
    }
    try writer.writeAll(" ::=");
    for (rp.rhs, rp.rhsalias) |sp, alias| {
        if (sp.type == .multiterminal) {
            try writer.print(" {s}", .{sp.subsym[0].name});
            for (sp.subsym[1..]) |ssp| {
                try writer.print("|{s}", .{ssp.name});
            }
        } else {
            try writer.print(" {s}", .{sp.name});
        }
        if (comptime print_aliases) {
            if (alias.len > 0) try writer.print("({s})", .{alias});
        }
    }
}

// /* Duplicate the input file without comments and without actions
// ** on rules */
// void Reprint(struct lemon *lemp)
// {
//   struct rule *rp;
//   struct symbol *sp;
//   int i, j, maxlen, len, ncolumns, skip;
//   printf("// Reprint of input file \"%s\".\n// Symbols:\n",lemp->filename);
//   maxlen = 10;
//   for(i=0; i<lemp->nsymbol; i++){
//     sp = lemp->symbols[i];
//     len = lemonStrlen(sp->name);
//     if( len>maxlen ) maxlen = len;
//   }
//   ncolumns = 76/(maxlen+5);
//   if( ncolumns<1 ) ncolumns = 1;
//   skip = (lemp->nsymbol + ncolumns - 1)/ncolumns;
//   for(i=0; i<skip; i++){
//     printf("//");
//     for(j=i; j<lemp->nsymbol; j+=skip){
//       sp = lemp->symbols[j];
//       assert( sp->index==j );
//       printf(" %3d %-*.*s",j,maxlen,maxlen,sp->name);
//     }
//     printf("\n");
//   }
//   for(rp=lemp->rule; rp; rp=rp->next){
//     rule_print(stdout, rp);
//     printf(".");
//     if( rp->precsym ) printf(" [%s]",rp->precsym->name);
//     /* if( rp->code ) printf("\n    %s",rp->code); */
//     printf("\n");
//   }
// }
//

/// Print a single rule.
fn RulePrint(writer: anytype, rp: *Rule, iCursor: ?usize) !void {
    try writer.print("{s} ::=", .{rp.lhs.name});
    for (0..rp.rhs.len + 1) |i| {
        if (i == iCursor) try writer.writeAll(" *");
        if (i == rp.rhs.len) break;
        const sp = rp.rhs[i];
        if (sp.type == .multiterminal) {
            try writer.print(" {s}", .{sp.subsym[0].name});
            for (sp.subsym[1..]) |ssp| {
                try writer.print("|{s}", .{ssp.name});
            }
        } else {
            try writer.print(" {s}", .{sp.name});
        }
    }
}

/// Print the rule for a configuration.
fn ConfigPrint(writer: anytype, cfp: *Config) !void {
    try RulePrint(writer, cfp.rp, cfp.dot);
}

// TODO: SetPrint goes here
// TODO: PlinkPrint goes here

// Print an action to the given file descriptor.  Return FALSE if
// nothing was actually printed.
fn PrintAction(writer: anytype, ap: *Action, indent: usize) !bool {
    var printed = true;
    switch (ap.type) {
        .shift => {
            try writer.print("{[name]s: >[width]} shift        {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.stp.statenum,
            });
        },
        .reduce => {
            try writer.print("{[name]s: >[width]} reduce       {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
            try RulePrint(writer, ap.x.rp.?, null);
        },
        .shiftreduce => {
            try writer.print("{[name]s: >[width]} shift-reduce {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
            try RulePrint(writer, ap.x.rp.?, null);
        },
        .accept => {
            try writer.print("{[name]s: >[width]} accept", .{
                .name = ap.sp.name,
                .width = indent,
            });
        },
        .@"error" => {
            try writer.print("{[name]s: >[width]} error", .{
                .name = ap.sp.name,
                .width = indent,
            });
        },
        .rrconflict, .srconflict => {
            try writer.print("{[name]s: >[width]} reduce       {[st]d: <7} ** Parsing conflict **", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
        },
        .ssconflict => {
            try writer.print("{[name]s: >[width]} shift        {[st]d: <7} ** Parsing conflict **", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.stp.statenum,
            });
        },
        .sh_resolved => {
            if (showPrecendenceConflict) {
                try writer.print("{[name]s: >[width]} shift        {[st]d: <7} -- dropped by precedence", .{
                    .name = ap.sp.name,
                    .width = indent,
                    .st = ap.x.stp.statenum,
                });
            } else {
                printed = false;
            }
        },
        .rd_resolved => {
            if (showPrecendenceConflict) {
                try writer.print(
                    "{[name]s: >[width]} reduce       {[st]d: <7} -- dropped by precedence",
                    .{
                        .name = ap.sp.name,
                        .width = indent,
                        .st = ap.x.rp.?.iRule,
                    },
                );
            } else {
                printed = false;
            }
        },
        .not_used => {
            printed = false;
        },
        ._not_initialized => unreachable,
    }
    if (printed) {
        if (ap.spOpt) |spOpt| {
            try writer.print("  /* because {s}=={s} */", .{ ap.sp.name, spOpt.name });
        }
    }
    return printed;
}

/// Generate the "*.out" log file
fn ReportOutput(lemp: *Lemon) !void {
    const m_fh = try file_open(lemp, ".zig.out", .{});
    if (m_fh) |fh| {
        defer fh.close();
        const f_writer = fh.writer();
        var write_buffer = std.io.bufferedWriter(f_writer);
        const b_writer = write_buffer.writer();
        try reportOutputImpl(lemp, b_writer);
        try write_buffer.flush();
    } else {
        return; // No file handle
    }
}

/// Write the report to the provided writer.
fn reportOutputImpl(lemp: *Lemon, writer: anytype) !void {
    for (0..lemp.nxstate) |i| {
        const stp = lemp.sorted[i];
        try writer.print("State {d}:\n", .{stp.statenum});
        var m_cfp: ?*Config = if (lemp.basisflag) stp.cfp else stp.bp;
        while (m_cfp) |cfp| {
            var buf: [20]u8 = .{0} ** 20;
            if (cfp.dot == cfp.rp.rhs.len) {
                const dot_s = try std.fmt.bufPrint(&buf, "({d})", .{cfp.rp.iRule});
                try writer.print("    {s:>5} ", .{dot_s});
            } else {
                try writer.writeByteNTimes(' ', 10);
            }
            try ConfigPrint(writer, cfp);
            try writer.writeByte('\n');
            if (lemp.basisflag) {
                m_cfp = cfp.next;
            } else {
                m_cfp = cfp.bp;
            }
        }
        try writer.writeByte('\n');
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (try PrintAction(writer, ap, 30)) try writer.writeByte('\n');
        }
        try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Symbols:\n");
    try writer.writeAll("The first-set of non-terminals is shown after the name.\n\n");
    for (lemp.symbols[0..lemp.nsymbol], 0..) |sp, i| {
        try writer.print("  {d:>3}: {s}", .{ i, sp.name });
        if (sp.type == .nonterminal) {
            try writer.writeByte(':');
            if (sp.lambda) {
                try writer.writeAll(" <lambda>");
            }
            for (0..lemp.nterminal) |j| {
                if (sp.firstset.len > 0 and sp.firstset[j]) {
                    try writer.print(" {s}", .{lemp.symbols[j].name});
                }
            }
        }
        if (sp.prec) |prec| try writer.print(" (precedence={d})", .{prec});
        try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Syntax-only Symbols:\n");
    try writer.writeAll("The following symbols never carry semantic content.\n\n");
    {
        var n: usize = 0;
        for (0..lemp.nsymbol) |i| {
            const sp = lemp.symbols[i];
            if (sp.bContent) continue;
            const w = sp.name.len;
            if (n > 0 and n + w > 75) {
                try writer.writeByte('\n');
                n = 0;
            }
            if (n > 0) {
                try writer.writeByte(' ');
                n += 1;
            }
            try writer.print("{s}", .{sp.name});
            n += w;
        }
        if (n > 0) try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Rules:\n");
    {
        var m_rp: ?*Rule = lemp.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            try writer.print("{d:>4}: ", .{rp.iRule});
            try rule_print(writer, rp);
            try writer.writeByte('.');
            if (rp.precsym) |precsym| {
                try writer.print(" [{s} precedence={d}]", .{ precsym.name, precsym.prec.? });
            }
            try writer.writeByte('\n');
        }
    }
}

/// The state vector for the entire parser generator is recorded as
/// follows.  (LEMON uses no global variables and makes little use of
/// static variables.  Fields in the following structure can be thought
/// of as being global variables in the program.)
const Lemon = struct {
    /// Allocator
    allocator: Allocator,
    /// Table of states sorted by state number
    sorted: []*State,
    /// List of all rules
    rule: *Rule,
    /// First rule
    startRule: *Rule,
    /// Number of states
    nstate: u32,
    /// nstate with tail degenerate states removed
    nxstate: u32,
    /// Number of rules
    nrule: u32,
    /// Number of rules with actions
    nruleWithAction: usize,
    /// Number of terminal and nonterminal symbols
    nsymbol: usize,
    /// Number of terminal symbols
    nterminal: usize,
    /// Minimum shift-reduce action value
    minShiftReduce: u32,
    /// Error action value
    errAction: u32,
    /// Accept action value
    accAction: u32,
    /// No-op action value
    noAction: u32,
    /// Minimum reduce action
    minReduce: u32,
    /// Maximum action value of any kind
    maxAction: u32,
    /// Sorted array of pointers to symbols
    symbols: []*Symbol,
    /// Number of errors
    errorcnt: usize,
    /// The error symbol
    errsym: ?*Symbol,
    ///  Token that matches anything
    wildcard: ?*Symbol,
    /// Name of the generated parser
    name: []u8,
    /// Declaration of the 3rd argument to parser
    arg: []u8,
    /// Declaration of 2nd argument to constructor
    ctx: []u8,
    /// Type of terminal symbols in the parser stack
    tokentype: []u8,
    /// The default type of non-terminal symbols
    vartype: []u8,
    /// Name of the start symbol for the grammar
    start: []u8,
    /// Size of the parser stack
    stacksize: []u8,
    /// Code to put at the start of the C file
    include: []u8,
    /// Code to execute when an error is seen
    @"error": []u8,
    /// Code to execute on a stack overflow
    overflow: []u8,
    /// Code to execute on parser failure
    failure: []u8,
    /// Code to execute when the parser excepts
    accept: []u8,
    /// Code appended to the generated file
    extracode: []u8,
    /// Code to execute to destroy token data
    tokendest: []u8,
    /// Code for the default non-terminal destructor
    vardest: []u8,
    /// Name of the input file
    filename: []const u8,
    /// Name of the current output file
    outname: []u8,
    /// A prefix added to token names in the .h file
    tokenprefix: []u8,
    /// Function to use to allocate stack space
    reallocFunc: []u8,
    /// Function to use to free stack space
    freeFunc: []u8,
    nconflict: u32,
    nactiontab: int,
    nlookaheadtab: int,
    tablesize: int,
    basisflag: bool,
    printPreprocessed: bool,
    has_fallback: bool,
    nolineosflag: bool,
    argv: [][:0]u8,

    // TODO: we leave several things undefined here which are not
    // guaranteed to be defined in the presence of bad inputs.
    // This can be fixed by making dummy rules which point to
    // dummy symbols, as threadlocal vars (but these we keep).
    // --
    // It is admittedly more convenient to have pointers be always
    // nullable, when it comes to this kind of thing.  Although
    // really this problem is created by that semantic more than it
    // is solved by it, since in Zig we would take more pains while
    // writing code like this to point at valid data as soon as we
    // meaningfully can.

    pub const empty: Lemon = .{
        .allocator = undefined,
        .sorted = &.{},
        .rule = undefined,
        .startRule = undefined,
        .nstate = 0,
        .nxstate = 0,
        .nrule = 0,
        .nruleWithAction = 0,
        .nsymbol = 0,
        .nterminal = 0,
        .minShiftReduce = 0,
        .errAction = 0,
        .accAction = 0,
        .noAction = 0,
        .minReduce = 0,
        .maxAction = 0,
        .symbols = &.{},
        .errorcnt = 0,
        .errsym = null,
        .wildcard = null,
        .name = &.{},
        .arg = &.{},
        .ctx = &.{},
        .tokentype = &.{},
        .vartype = &.{},
        .start = &.{},
        .stacksize = &.{},
        .include = &.{},
        .@"error" = &.{},
        .overflow = &.{},
        .failure = &.{},
        .accept = &.{},
        .extracode = &.{},
        .tokendest = &.{},
        .vardest = &.{},
        .filename = "",
        .outname = &.{},
        .tokenprefix = &.{},
        .reallocFunc = &.{},
        .freeFunc = &.{},
        .nconflict = 0,
        .nactiontab = 0,
        .nlookaheadtab = 0,
        .tablesize = 0,
        .basisflag = false,
        .printPreprocessed = false,
        .has_fallback = false,
        .nolineosflag = false,
        .argv = &.{},
    };

    pub fn create(allocator: Allocator) !*Lemon {
        const gp = try allocator.create(Lemon);
        errdefer allocator.destroy(gp);
        gp.* = .empty;
        gp.allocator = allocator;
        gp.sorted = try allocator.alloc(*Symbol, 0);
        errdefer allocator.free(gp.sorted);
        gp.name = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.name);
        gp.arg = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.arg);
        gp.ctx = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.ctx);
        gp.tokentype = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokentype);
        gp.vartype = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.vartype);
        gp.start = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.start);
        gp.stacksize = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.stacksize);
        gp.include = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.include);
        gp.@"error" = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.@"error");
        gp.overflow = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.overflow);
        gp.failure = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.failure);
        gp.accept = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.accept);
        gp.extracode = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.extracode);
        gp.tokendest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokendest);
        gp.vardest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.vardest);
        gp.filename = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.filename);
        gp.outname = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.outname);
        gp.tokenprefix = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokenprefix);
        gp.reallocFunc = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.reallocFunc);
        gp.argv = undefined; // populated by std.process.argsAlloc.
        return gp;
    }

    pub fn destroy(gp: *Lemon, allocator: Allocator) void {
        allocator.free(gp.sorted);
        allocator.free(gp.name);
        allocator.free(gp.arg);
        allocator.free(gp.ctx);
        allocator.free(gp.tokentype);
        allocator.free(gp.vartype);
        allocator.free(gp.start);
        allocator.free(gp.stacksize);
        allocator.free(gp.include);
        allocator.free(gp.@"error");
        allocator.free(gp.overflow);
        allocator.free(gp.failure);
        allocator.free(gp.accept);
        allocator.free(gp.extracode);
        allocator.free(gp.tokendest);
        allocator.free(gp.vardest);
        allocator.free(gp.outname);
        allocator.free(gp.tokenprefix);
        allocator.free(gp.reallocFunc);
        allocator.destroy(gp);
    }
};

//| [324] Action stuff

// Some of this got distributed to struct namespaces

//|
//| The state of the yy_action table under construction is an instance of
//| the following structure.
//|
//| The yy_action table maps the pair (state_number, lookahead) into an
//| action_number.  The table is an array of integers pairs.  The state_number
//| determines an initial offset into the yy_action array.  The lookahead
//| value is then added to this initial offset to get an index X into the
//| yy_action array. If the aAction[X].lookahead equals the value of the
//| of the lookahead input, then the value of the action_number output is
//| aAction[X].action.  If the lookaheads do not match then the
//| default action for the state_number is returned.
//|
//| All actions associated with a single state_number are first entered
//| into aLookahead[] using multiple calls to acttab_action().  Then the
//| actions for that single state_number are placed into the aAction[]
//| array with a single call to acttab_insert().  The acttab_insert() call
//| also resets the aLookahead[] array in preparation for the next
//| state number.

/// Value of the lookahead token
/// Action to take on the given lookahead
const LookaheadAction = struct {
    /// Value of the lookahead token
    lookahead: i32,
    /// Action to take on the given lookahead
    action: i32,

    pub const empty: LookaheadAction = .{ .lookahead = -1, .action = -1 };
};

const ActTable = struct {
    allocator: Allocator,
    /// The yyaction[] table under construction
    aAction: ArrayList(LookaheadAction) = .empty,
    /// Number of aAction slots in actual use
    nAction: usize = 0,
    /// A single new transaction set
    aLookahead: ArrayList(LookaheadAction) = .empty,
    /// Minimum aLookahead[].lookahead
    mnLookahead: i32 = 0,
    /// Action associated with mnLookahead
    mnAction: i32 = 0,
    /// Maximum aLookahead[].lookahead
    mxLookahead: i32 = 0,
    /// Number of terminal symbols
    nterminal: usize = 0,
    /// total number of symbols
    nsymbol: usize = 0,

    // [541] Action_add
    pub fn create(allocator: Allocator, nsymbol: usize, nterminal: usize) !*ActTable {
        var tab = try allocator.create(ActTable);
        tab.* = .{};
        tab.nsymbol = nsymbol;
        tab.nterminal = nterminal;
        tab.allocator = allocator;
        return tab;
    }

    pub fn destroy(tab: *ActTable) void {
        tab.aAction.deinit(tab.allocator);
        tab.aLookahead.deinit(tab.allocator);
        tab.allocator.destroy(tab);
    }

    /// Return the number of entries in the yy_action table
    pub inline fn lookaheadSize(x: *const ActTable) usize {
        return x.aAction.items.len;
    }

    /// The value for the N-th entry in yy_action
    pub inline fn yyaction(tab: *const ActTable, n: usize) i32 {
        return tab.aAction.items[n].action;
    }

    /// The value for the N-th entry in yy_lookahead
    pub inline fn yylookahead(tab: *const ActTable, n: usize) i32 {
        return tab.aAction.items[n].lookahead;
    }

    // [639]
    /// Add a new action to the current transaction set.
    ///
    /// This routine is called once for each lookahead for a particular
    /// state.
    pub fn action(tab: *ActTable, lookahead: i32, an_action: i32) !void {
        if (tab.aLookahead.items.len >= tab.aLookahead.capacity) {
            try tab.aLookahead.ensureUnusedCapacity(tab.allocator, 25);
        }
        if (tab.aLookahead.items.len == 0) {
            tab.mxLookahead = lookahead;
            tab.mnLookahead = lookahead;
            tab.mnAction = an_action;
        } else {
            if (tab.mxLookahead < lookahead) tab.mxLookahead = lookahead;
            if (tab.mnLookahead > lookahead) {
                tab.mnLookahead = lookahead;
                tab.mnAction = an_action;
            }
        }
        tab.aLookahead.appendAssumeCapacity(
            tab.allocator,
            .{ .lookahead = lookahead, .action = an_action },
        );
    }

    // [683]
    /// Add the transaction set built up with prior calls to acttab_action()
    /// into the current action table.  Then reset the transaction set back
    /// to an empty set in preparation for a new round of acttab_action() calls.
    ///
    /// Return the offset into the action table of the new transaction.
    ///
    /// If the makeItSafe parameter is true, then the offset is chosen so that
    /// it is impossible to overread the yy_lookaside[] table regardless of
    /// the lookaside token.  This is done for the terminal symbols, as they
    /// come from external inputs and can contain syntax errors.  When makeItSafe
    /// is false, there is more flexibility in selecting offsets, resulting in
    /// a smaller table.  For non-terminal symbols, which are never syntax errors,
    /// makeItSafe can be false.
    ///
    pub fn insert(p: *ActTable, makeItSafe: bool) !i32 {
        //  Make sure we have enough space to hold the expanded action table
        // in the worst case.  The worst case occurs if the transaction set
        // must be appended to the current action table.
        assert(p.aLookahead.items.len > 0);
        {
            const n = p.nsymbol + 1;
            if (p.nAction + n >= p.aAction.items.len) {
                // TODO: This value is probably excessive.
                const new_cap = p.nAction + p.aAction.items.len + 20;
                const new_slice = try p.aAction.addManyAsSlice(p.allocator, new_cap);
                @memset(new_slice, LookaheadAction.empty);
            }
        }
        const end = if (makeItSafe) p.mnLookahead else 0;
        // Since we're done allocating, these pointers are stable:
        const act_items = p.aAction.items;
        const look_items = p.aLookahead.items;
        var ii: isize = p.nAction - 1;
        i_loop: while (ii >= end) : (ii -= 1) {
            const i: usize = @intCast(ii);
            if (act_items[i].lookahead == p.mnLookahead) {
                // All lookaheads and actions in the aLookahead[] transaction
                // must match against the candidate aAction[i] entry.
                if (act_items[i].action != p.mnAction) continue :i_loop;
                var j: usize = 0;
                j_loop: while (j < look_items.len) : (j += 1) {
                    const k = look_items[j].lookahead - p.mnLookahead + i;
                    if (k < 0 or k > p.nAction) break :j_loop;
                    if (look_items[j].lookahead != act_items[k].lookahead) break :j_loop;
                    if (look_items[j].action != act_items[k].action) break :j_loop;
                }
                if (j < look_items.len) continue :i_loop;

                // No possible lookahead value that is not in the aLookahead[]
                // transaction is allowed to match aAction[i]
                var n: i32 = 0;
                j = 0;
                j_check: while (j < p.nAction) : (j += 1) {
                    if (act_items[j].lookahead < 0) continue :j_check;
                    if (act_items[j].lookahead == j + p.mnLookahead + i) n += 1;
                }

                if (n == look_items.len) {
                    break :i_loop; //An exact match is found at offset i
                }
            }
        }
        // If no existing offsets exactly match the current transaction, find an
        // an empty offset in the aAction[] table in which we can add the
        // aLookahead[] transaction.
        if (ii < end) {
            // Look for holes in the aAction[] table that fit the current
            // aLookahead[] transaction.  Leave i set to the offset of the hole.
            // If no holes are found, i is left at p->nAction, which means the
            // transaction will be appended.
            var i: usize = if (makeItSafe) @intCast(p.mnLookahead) else 0; // Isn't this 'end'? -Sam
            i_loop: while (i < act_items.len - p.mxLookahead) : (i += 1) {
                if (act_items[i].lookahead < 0) {
                    var j: usize = 0;
                    j_loop: while (j < look_items.len) : (j += 1) {
                        const k = look_items[i].lookahead - p.mxLookahead + i;
                        if (k < 0) break :j_loop;
                        if (act_items[k].lookahead >= 0) break :j_loop;
                    }
                    if (j < look_items.len) continue :i_loop;
                    j = 0;
                    j_check: while (j < act_items.len) : (j += 1) {
                        if (act_items[j].lookahead == j + p.mnLookahead - i) break :j_check;
                    }
                    if (j == act_items.len) {
                        break :i_loop; // Fits in empty slots
                    }
                }
            }
        }
        // Insert transaction set at index i.
        for (0..look_items.len) |j| {
            const k = look_items[j] - p.mnLookahead + ii;
            act_items[cast(usize, k)] = look_items[j];
            if (k > p.nAction) p.nAction = k + 1;
        }

        if (makeItSafe and ii + p.nterminal >= p.nAction) p.nAction = ii + p.nterminal + 1;

        p.aLookahead.clearRetainingCapacity();

        // Return the offset that is added to the lookahead in order to get the
        // index into yy_action of the action
        return ii - p.mnLookahead;
    }

    // [792]
    /// Return the size of the action table without the trailing syntax error entries.
    pub fn actionSize(acttab: *ActTable) usize {
        var n = acttab.nAction;
        while (n > 0 and acttab.aAction.items[n].lookahead < 0) : (n -= 1) {}
        return n;
    }
};

// [803]
///
/// Find a precedence symbol of every rule in the grammar.
///
/// Those rules which have a precedence symbol coded in the input
/// grammar using the "[symbol]" construct will already have the
/// rp->precsym field filled.  Other rules take as their precedence
/// symbol the first RHS symbol with a defined precedence.  If there
/// are not RHS symbols with a defined precedence, the precedence
/// symbol field is left blank.
fn FindRulePrecedences(lem: *Lemon) void {
    var maybe_rp: ?*Rule = lem.rule;
    while (maybe_rp) |rp| : (maybe_rp = rp.next) {
        if (rp.precsym == null) {
            var i: usize = 0;
            while (i < rp.nrhs and rp.precsym == null) : (i += 1) {
                const sp: *Symbol = rp.rhs[i];
                if (sp.type == .multiterminal) {
                    var j: usize = 0;
                    j_loop: while (j < sp.nsubsym) : (j += 1) {
                        if (sp.subsym[j].prec) |_| {
                            rp.precsym = sp.subsym[j];
                            break :j_loop;
                        }
                    }
                } else if (sp.prec) |_| {
                    rp.precsym = rp.rhs[i];
                }
            }
        }
    }
}

// [842]
/// Find all nonterminals which will generate the empty string.
/// Then go back and compute the first sets of every nonterminal.
/// The first set is the set of all terminal symbols which can begin
/// a string generated by that nonterminal.
fn FindFirstSets(lemp: *Lemon) !void {
    for (lemp.symbols) |sym| {
        dbgassert(sym.lambda == false);
    }
    for (lemp.nterminal..lemp.nsymbol) |i| {
        const sym = lemp.symbols[i];
        dbgassert(sym.type == .nonterminal);
        sym.firstset = try lemp.allocator.alloc(bool, set_size);
    }
    // First compute all lambdas
    var progress: bool = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = lemp.rule;
        walk: while (rp) |rule| : (rp = rule.next) {
            if (rule.lhs.lambda) continue :walk;
            var i: usize = 0;
            sym: while (i < rule.nrhs) : (i += 1) { // TODO: just rule.rhs yeah
                const sp = rule.rhs[i];
                dbgassert(sp.type == .nonterminal or sp.lambda == false);
                if (sp.lambda == false) break :sym;
            } // A rule with no nrhs, or, all lambda, is lambda.
            if (i == rule.nrhs) {
                rule.lhs.lambda = true;
                progress = true;
            }
        }
    }

    // Now compute all first sets
    progress = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = lemp.rule;
        while (rp) |rule| : (rp = rule.next) {
            const s1 = rule.lhs;
            rhs: for (rule.rhs) |s2| {
                if (s2.type == .terminal) {
                    const p = SetAdd(s1.firstset, s2.index);
                    progress = progress or p;
                    break :rhs;
                } else if (s2.type == .multiterminal) {
                    for (s2.subsym) |ss2| {
                        const p = SetAdd(s1.firstset, ss2.index);
                        progress = progress or p;
                    }
                    break :rhs;
                } else if (s1 == s2) {
                    if (s1.lambda == false) break :rhs;
                } else {
                    const p = SetUnion(s1.firstset, s2.firstset);
                    progress = progress or p;
                    if (s2.lambda == false) break :rhs;
                }
            }
        }
    }
}

// [900]
//
// Compute all LR(0) states for the grammar.  Links
// are added to between some states so that the LR(1) follow sets
// can be computed later.
//
fn FindStates(lemp: *Lemon) !void {
    const sp: *Symbol = sp: {
        if (lemp.start.len > 0) {
            const maybe_sp = Symbol_find(lemp.start);
            if (maybe_sp) |_| {
                break :sp lemp.startRule.lhs;
            } else {
                ErrorMsg(lemp.filename, 0, "" ++
                    "The specified start symbol \"{s}\" is not " ++
                    "in a nonterminal of the grammar.  \"{s}\" will be used as the start " ++
                    "symbol instead.", .{ lemp.start, lemp.startRule.lhs.name });
                lemp.errorcnt += 1;
                break :sp lemp.startRule.lhs;
            }
        } else {
            // OG checks if startRule pointer is defined, we (and it) ensure
            // that it is before we get here.
            break :sp lemp.startRule.lhs;
        }
    };
    // Make sure the start symbol doesn't occur on the right-hand side of
    // any rule.  Report an error if it does.  (YACC would generate a new
    // start symbol in this case.)
    var rp: ?*Rule = lemp.rule;
    while (rp) |rule| : (rp = rule.next) {
        for (rule.rhs) |rhs| {
            if (rhs == sp) {
                ErrorMsg(lemp.filename, 0, "" ++
                    "The start symbol \"{s}\" occurs on the " ++
                    "right-hand side of a rule. This will result in a parser which " ++
                    "does not work properly.", .{sp.name});
                lemp.errorcnt += 1;
            }
            //| NOTE: the previous comparison says FIX ME:  Deal with multiterminals.
            //| I think this is the fix, but we leave it out of lemon classic because
            //| I aim to be mostly bug-compatible.  It's not actually clear this condition
            //| can be triggered in any case.
            if (!lemon_classic) if (rhs.type == .multiterminal) {
                for (rhs.subsym) |subsym| {
                    if (subsym == sp) {
                        ErrorMsg(lemp.filename, 0, "" ++
                            "The start symbol {s} appears as a terminal in a multiterminal. " ++
                            "This was thought to be impossible.", .{sp.name});
                        lemp.errorcnt += 1;
                    }
                }
            };
        }
    }
    // The basis configuration set for the first state
    // is all rules which have the start symbol as their
    // left-hand side.
    rp = sp.rule;
    while (rp) |rule| : (rp = rule.nextlhs) {
        rule.lhsStart = true;
        const new_cfp = try Configlist_addbasis(rule, 0);
        _ = SetAdd(new_cfp.fws, 0);
    }

    // Compute the first state.  All other states will be
    // computed automatically during the computation of the first one.
    // The returned pointer to the first state is not used.
    _ = try getstate(lemp);
}

threadlocal var state_count: usize = 0;

// [967]
// Return a pointer to a state which is described by the configuration
// list which has been built from calls to Configlist_add.
fn getstate(lemp: *Lemon) Allocator.Error!*State {
    // Extract the sorted basis of the new state.  The basis was constructed
    // by prior calls to "Configlist_addbasis()".
    Configlist_sortbasis();
    const maybe_bp = Configlist_basis();
    if (p_check1) {
        state_count += 1;
        dprint("State basis {d}: ", .{state_count});
        var mbp = maybe_bp;
        while (mbp) |bp| : (mbp = bp.bp) {
            if (bp.dot < bp.rp.rhs.len) {
                dprint("{s}:{d} #({d}) {s} ", .{ bp.rp.lhs.name, bp.rp.iRule, bp.dot, bp.rp.rhs[bp.dot].name });
            } else {
                dprint("{s}:{d} #({d}) [end] ", .{ bp.rp.lhs.name, bp.rp.iRule, bp.dot });
            }
        }
        dprint("\n", .{});
    }
    const maybe_stp = if (maybe_bp) |bp| State_find(bp) else null;
    if (maybe_stp) |stp| {
        if (p_check1) {
            dprint("  state found: {d}\n", .{stp.statenum});
        }
        // A state with the same basis already exists!  Copy all the follow-set
        // propagation links from the state under construction into the
        // preexisting state, then return a pointer to the preexisting state
        var maybe_x: ?*Config = maybe_bp;
        var maybe_y: ?*Config = stp.bp;
        while (maybe_x != null and maybe_y != null) {
            const x = maybe_x.?;
            const y = maybe_y.?;
            Plink_copy(&y.bplp, x.bplp);
            Plink_delete(x.fplp);
            x.fplp = null;
            x.bplp = null;
            maybe_x = x.bp;
            maybe_y = y.bp;
        }
        Configlist_eat(Configlist_return(), lemp.allocator);
        return stp;
    } else {
        // This really is a new state.  Construct all the details
        if (p_check1) {
            dprint("  state not found\n", .{});
        }
        try Configlist_closure(lemp); //  Compute the configuration closure */
        Configlist_sort(); //  Sort the configuration closure */
        const cfp = Configlist_return().?; //  Get a pointer to the config list */
        if (p_check1) {
            dprint("cfp: ", .{});
            var cfp_count: usize = 0;
            var mcfp: ?*Config = cfp;
            while (mcfp) |a_cfp| : (mcfp = a_cfp.next) {
                cfp_count += 1;
                dprint("*", .{});
            }
            dprint(" ({d})\n", .{cfp_count});
        }
        const stp = try State_new(); //  A new state structure */
        stp.bp = maybe_bp.?;
        stp.cfp = cfp;
        stp.statenum = lemp.nstate;
        lemp.nstate += 1;
        stp.ap = null;
        dbgassert(try State_insert(stp, stp.bp.?));
        try buildshifts(lemp, stp);
        return stp;
    }
}

///
/// Return true if two symbols are the same.
///
fn same_symbol(a: *const Symbol, b: *const Symbol) bool {
    if (a == b) return true;
    if (a.type != .multiterminal) return false;
    if (b.type != .multiterminal) return false;
    if (a.subsym.len != b.subsym.len) return false;
    for (a.subsym, b.subsym) |asub, bsub| {
        if (asub != bsub) return false;
    }
    return true;
}

fn buildshifts(lemp: *Lemon, stp: *State) !void {
    var maybe_cfp: ?*Config = stp.cfp; // For looping thru the config closure of "stp"
    // Initialize with a conveniently available symbol, this is never used:
    // /* Each configuration becomes complete after it contributes to a successor
    // ** state.  Initially, all configurations are incomplete.
    if (p_check_next) {
        dprint("buildshifts entry on stp {d}\n", .{stp.statenum});
    }
    while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
        if (p_check_next) dprint("Reset cfg {d}-{d}\n", .{ cfp.rp.iRule, cfp.dot });
        cfp.status = .incomplete;
    }
    maybe_cfp = stp.cfp;
    //   /* Loop through all configurations of the state "stp".
    while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
        if (p_debug) dprint("outer config {s}: {s} dot ({d}) nrhs {d} len {d} ", .{
            cfp.rp.lhs.name,
            @tagName(cfp.status),
            cfp.dot,
            cfp.rp.nrhs,
            cfp.rp.rhs.len,
        });
        if (cfp.status == .complete) continue; // Already used by inner loop
        if (cfp.dot >= cfp.rp.rhs.len) continue; // Can't shift this config
        Configlist_reset(); // Reset the new config set
        const sp = cfp.rp.rhs[cfp.dot]; // Symbol following the dot in configuration "cfp"
        var maybe_bcfp: ?*Config = cfp; // For the inner loop on config closure of "stp"
        while (maybe_bcfp) |bcfp| : (maybe_bcfp = bcfp.next) {
            if (bcfp.status == .complete) continue; // Already used
            if (bcfp.dot >= bcfp.rp.rhs.len) continue; // Can't shift this one
            const bsp = bcfp.rp.rhs[bcfp.dot]; //  Get symbol after dot
            if (!same_symbol(bsp, sp)) continue; //  Must be same as for "cfp"
            bcfp.status = .complete; //  Mark this config as used
            if (p_check_next) {
                dprint("  basis from {s}: {d} -> {d}\n", .{
                    bcfp.rp.lhs.name,
                    bcfp.dot,
                    bcfp.dot + 1,
                });
            }
            const newcfg = try Configlist_addbasis(bcfp.rp, bcfp.dot + 1);
            try Plink_add(&newcfg.bplp, bcfp);
        }
        // /* Get a pointer to the state described by the basis configuration set
        // ** constructed in the preceding loop */
        const newstp = try getstate(lemp);
        // /* The state "newstp" is reached from the state "stp" by a shift action
        // ** on the symbol "sp" */
        if (sp.type == .multiterminal) {
            for (sp.subsym) |subsym| {
                try Action.addState(&stp.ap, .shift, subsym, newstp);
            }
        } else {
            try Action.addState(&stp.ap, .shift, sp, newstp);
        }
    }
}

//| [1077]

///
/// Construct the propagation links
///
fn FindLinks(lemp: *Lemon) !void {

    // /* Housekeeping detail:
    // ** Add to every propagate link a pointer back to the state to
    // ** which the link is attached. */
    for (0..lemp.nstate) |i| {
        const stp: ?*State = lemp.sorted[i];
        var maybe_cfp: ?*Config = stp.?.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            if (p_check1) {
                dprint("cfp: {s}:{d} -> {d}\n", .{ cfp.rp.lhs.name, cfp.rp.index, stp.?.statenum });
            }
            cfp.stp = stp;
        }
    }

    // /* Convert all backlinks into forward links.  Only the forward
    // ** links are used in the follow-set computation. */
    for (0..lemp.nstate) |i| {
        const stp: ?*State = lemp.sorted[i];
        var maybe_cfp = if (stp) |sp| sp.cfp else null;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            if (p_check1) {
                dprint("cfp: {s}:{d} <-> ", .{ cfp.rp.lhs.name, cfp.rp.index });
            }
            var maybe_plp: ?*PLink = cfp.bplp;
            while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                var other = plp.cfp;
                if (p_check1) {
                    dprint("{s}:{d} ({d}), ", .{ other.rp.lhs.name, other.rp.index, other.dot });
                }
                try Plink_add(&other.fplp, cfp);
            }
            if (p_check1) dprint("\n", .{});
        }
    }
}

// [1112]
// Compute all followsets.
//
// A followset is the set of all symbols which can come immediately
// after a configuration.
fn FindFollowSets(lemp: *Lemon) void {
    for (lemp.sorted) |stp| {
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            cfp.status = .incomplete;
        }
    }
    var c_count: usize = 0;
    var progress = true;
    while (progress) {
        progress = false;
        for (lemp.sorted) |stp| {
            var maybe_cfp: ?*Config = stp.cfp;
            states: while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
                if (cfp.status == .complete) continue :states;
                var maybe_plp: ?*PLink = cfp.fplp;
                while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                    const changed = SetUnion(plp.cfp.fws, cfp.fws);
                    if (p_check1) {
                        c_count += 1;
                        dprint(
                            "#{d} follow set: {s}:{d} ",
                            .{ c_count, plp.cfp.rp.lhs.name, plp.cfp.rp.index },
                        );
                        if (changed) {
                            dprint("change\n", .{});
                        } else {
                            dprint("no change\n", .{});
                        }
                    }
                    if (changed) {
                        plp.cfp.status = .incomplete;
                        progress = true;
                    }
                }
                cfp.status = .complete;
            }
        }
    }
}

// Compute the reduce actions, and resolve conflicts.
//
fn FindActions(lemp: *Lemon) !void {
    // Add all of the reduce actions
    // A reduce action is added for each element of the followset of
    // a configuration which has its dot at the extreme right.
    //
    for (lemp.sorted) |stp| { // Loop over all states
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) { // Loop over all configurations
            if (cfp.rp.rhs.len == cfp.dot) { // Is dot at extreme right?
                for (0..lemp.nterminal) |j| {
                    if (cfp.fws[j]) {
                        //  Add a reduce action to the state "stp" which will reduce by the
                        //  rule "cfp->rp" if the lookahead symbol is "lemp->symbols[j]"
                        try Action.addRule(&stp.ap, .reduce, lemp.symbols[j], cfp.rp);
                    }
                }
            }
        }
    }
    //  Add the accepting token
    const sp: *Symbol = sym: {
        if (lemp.start.len > 0) {
            const sp_start = Symbol_find(lemp.start);
            if (sp_start) |sps| {
                break :sym sps;
            } else {
                break :sym lemp.startRule.lhs;
            }
        } else break :sym lemp.startRule.lhs;
    };
    // Add to the first state (which is always the starting state of the
    // finite state machine) an action to ACCEPT if the lookahead is the
    // start nonterminal.
    try Action.addRule(&lemp.sorted[0].ap, .accept, sp, null);
    //   Resolve conflicts
    for (lemp.sorted) |stp| {
        stp.ap = if (stp.ap) |ap| Action.sort(ap) else null;
        var maybe_ap: ?*Action = stp.ap;
        while (maybe_ap) |ap| : (maybe_ap = ap.next) {
            var nap = ap.next;
            while (nap != null and nap.?.sp == ap.sp) : (nap = nap.?.next) {
                // The two actions "ap" and "nap" have the same lookahead.
                // Figure out which one should be used */
                if (p_check1) {
                    dprint("find state: before .{s} .{s}\n", .{ @tagName(ap.type), @tagName(nap.?.type) });
                }
                lemp.nconflict += resolve_conflict(ap, nap.?);
                if (p_check1) {
                    dprint("find state: after .{s} .{s}\n", .{ @tagName(ap.type), @tagName(nap.?.type) });
                }
            }
        }
    }
    // Report an error for each rule that can never be reduced.
    var m_rp: ?*Rule = lemp.rule;
    while (m_rp) |rp| : (m_rp = rp.next) rp.canReduce = false;
    for (lemp.sorted) |stp| {
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce) ap.x.rp.?.canReduce = true;
        }
    }
    m_rp = lemp.rule;
    while (m_rp) |rp| : (m_rp = rp.next) {
        if (rp.canReduce) continue;
        ErrorMsg(lemp.filename, 0, "" ++
            "This rule can not be reduced.\n", .{});
        lemp.errorcnt += 1;
    }
}

fn resolve_conflict(apx: *Action, apy: *Action) u32 {
    dbgassert(apx.sp == apy.sp); // Otherwise there would be no conflict
    var errcnt: u32 = 0;
    // TODO: This is the major overhaul to use a tagged union.
    if (apx.type == .shift and apy.type == .shift) {
        apy.type = .ssconflict;
        errcnt += 1;
    }
    if (apx.type == .shift and apy.type == .reduce) {
        const spx = apx.sp;
        const maybe_spy = apy.x.rp.?.precsym;
        if (maybe_spy == null) {
            // Not enough precedence information
            errcnt += 1; // And we can bail early
            return errcnt;
        } // So we can do this:
        const spy = maybe_spy.?;
        if (spx.prec == null or spy.prec == null) {
            // Not enough precedence information.
            apy.type = .srconflict;
            errcnt += 1;
        } else if (spx.prec.? > spy.prec.?) { // higher precedence wins
            apy.type = .rd_resolved;
        } else if (spx.prec.? < spy.prec.?) {
            apx.type = .sh_resolved;
        } else if (spx.prec.? == spy.prec.?) { // Use operator associativity to break tie
            if (spx.assoc == .right) {
                apy.type = .rd_resolved;
            } else if (spx.assoc == .left) {
                apx.type = .sh_resolved;
            } else {
                dbgassert(spx.assoc == .none);
                apx.type = .@"error"; // NOTE: no errcnt? hmm.
            }
        }
    } else if (apx.type == .reduce and apy.type == .reduce) {
        const maybe_spx = apx.x.rp.?.precsym;
        const maybe_spy = apy.x.rp.?.precsym;
        if (maybe_spx == null or maybe_spy == null or maybe_spx.?.prec == null or
            maybe_spy.?.prec == null or maybe_spx.?.prec.? == maybe_spy.?.prec.?)
        {
            apy.type = .rrconflict;
            errcnt += 1;
            return errcnt;
        }
        const spx = maybe_spx.?;
        const spy = maybe_spy.?;
        if (spx.prec.? > spy.prec.?) {
            apy.type = .rd_resolved;
        } else if (spx.prec.? < spy.prec.?) {
            apx.type = .rd_resolved;
        }
    } else {
        // The REDUCE/SHIFT case cannot happen because SHIFTs come before
        // REDUCEs on the list.  If we reach this point it must be because
        // the parser conflict had already been resolved.
        // zig fmt: off
        dbgassert(
            apx.type == .sh_resolved or
            apx.type == .rd_resolved or
            apx.type == .ssconflict or
            apx.type == .srconflict or
            apx.type == .rrconflict or

            apy.type == .sh_resolved or
            apy.type == .rd_resolved or
            apy.type == .ssconflict or
            apy.type == .srconflict or
            apy.type == .rrconflict
        );
        // zig fmt: on
    }
    return errcnt;
}
//| [1500] ErrorMsg

fn ErrorMsg(filename: []const u8, lineno: usize, comptime fmt: []const u8, args: anytype) void {
    std.debug.print("{s}:{d}: ", .{ filename, lineno });
    std.debug.print(fmt, args);
    std.debug.print("{s}", .{"\n"});
}

//| [2211] From parse.c

/// The state of the parser
const E_State = enum {
    initialize,
    waiting_for_decl_or_rule,
    waiting_for_decl_keyword,
    waiting_for_decl_arg,
    waiting_for_precedence_symbol,
    waiting_for_arrow,
    in_rhs,
    lhs_alias_1,
    lhs_alias_2,
    lhs_alias_3,
    rhs_alias_1,
    rhs_alias_2,
    precedence_mark_1,
    precedence_mark_2,
    resync_after_rule_error,
    resync_after_decl_error,
    waiting_for_destructor_symbol,
    waiting_for_datatype_symbol,
    waiting_for_fallback_id,
    waiting_for_wildcard_id,
    waiting_for_class_id,
    waiting_for_class_token,
    waiting_for_token_name,
};

pub const PState = struct {
    allocator: Allocator,
    /// Name of the input file
    filename: []const u8,
    /// Line number at which current token starts
    tokenlineno: usize,
    /// Number of errors so far
    errorcnt: usize,
    /// Start index of current token
    tokenstart: usize,
    /// Global state vector
    gp: *Lemon,
    /// The state of the parser
    state: E_State,
    /// The fallback token
    fallback: ?*Symbol,
    /// Token class symbol
    tkclass: *Symbol,
    /// Left-hand side of current rule
    lhs: *Symbol,
    /// Alias for the LHS
    lhsalias: []const u8,
    /// Number of right-hand side symbols seen
    nrhs: usize, // TODO: rhs.len right?
    /// RHS symbols
    rhs: []*Symbol,
    /// Aliases for each RHS symbol (or null)
    alias: [][]const u8, // We'll use empty slices as per usual
    /// Previous rule parsed
    prevrule: ?*Rule,
    /// Keyword of a declaration
    declkeyword: []const u8,
    /// Where the declaration argument should be put
    declargslot: ?*[]u8,
    /// Add `#line` before declaration insert
    insertLineMacro: bool,
    /// Where to write declaration line number
    decllinenoslot: ?*?u32, // The destination on Symbol is itself nullable.
    /// Assign this association to decl arguments
    declassoc: E_Assoc,
    /// Assign this precedence to decl arguments
    preccounter: u16,
    /// Pointer to first rule in the grammar
    firstrule: ?*Rule,
    /// Pointer to the most recently parsed rule
    lastrule: ?*Rule,

    pub const empty: PState = .{
        .allocator = undefined,
        .filename = "",
        .tokenlineno = 0,
        .tokenstart = 0,
        .errorcnt = 0,
        .gp = undefined,
        .state = .initialize,
        .fallback = null,
        .tkclass = &Symbol.start,
        .lhs = &Symbol.start,
        .lhsalias = "",
        .nrhs = 0,
        .rhs = &.{},
        .alias = &.{},
        .prevrule = null,
        .declkeyword = "",
        .declargslot = null,
        .insertLineMacro = false,
        .decllinenoslot = null,
        .declassoc = .unk,
        .preccounter = 0,
        .firstrule = null,
        .lastrule = null,
    };

    pub fn create(allocator: Allocator, gp: *Lemon) !*PState {
        var psp = try allocator.create(PState);
        errdefer allocator.destroy(psp);
        psp.* = .empty;
        psp.allocator = allocator;
        psp.gp = gp;
        psp.rhs = try allocator.alloc(*Symbol, MAXRHS);
        errdefer allocator.free(psp.rhs);
        psp.alias = try allocator.alloc([]const u8, MAXRHS);
        errdefer allocator.free(psp.alias);
        return psp;
    }

    // No clue how to dispose of things yet. But I think the answer is that Symbols all
    // live in the intern pool, with the strings, and we just nuke 'em at the end.
    // So...
    pub fn destroy(ps: *PState) void {
        ps.allocator.free(ps.rhs);
        ps.allocator.free(ps.alias);
        var rule_p = ps.firstrule;
        while (rule_p) |r| {
            const next = r.next;
            r.destroy(ps.allocator);
            rule_p = next;
        }
        ps.allocator.destroy(ps);
    }
};

// TODO: move the file stuff here, and use a stack psp like the OG
fn Parse(psp: *PState) !void {
    const file = if (std.fs.cwd().openFile(psp.filename, .{})) |f| file: {
        break :file f;
    } else |err| {
        // TODO: nicer message here
        std.debug.print("File open error {s}", .{@errorName(err)});
        exit(@truncate(@intFromError(err)));
    };
    defer file.close();
    const end_pos = try file.getEndPos();
    const filebuf = try psp.allocator.allocSentinel(u8, end_pos, 0);
    defer psp.allocator.free(filebuf);
    const read_bytes = try file.readAll(filebuf);
    if (read_bytes < end_pos) {
        std.debug.print("didnt read to end of file {s}\n", .{psp.filename});
        std.process.exit(1);
    }
    // /* Make an initial pass through the file to handle %ifdef and %ifndef */
    // preprocess_input(filebuf);
    // if( gp->printPreprocessed ){
    //   printf("%s\n", filebuf);
    //   return;
    // }
    //
    try scan(psp, filebuf);
    if (psp.gp.nrule > 0) {
        psp.gp.rule = psp.firstrule.?;
    }
    psp.gp.errorcnt = psp.errorcnt;
}

fn parseonetoken(psp: *PState, x_init: []const u8) !void {
    const x = try Strsafe(x_init);
    // This seems to be presumed (?)
    assert(x.len != 0);
    if (p_print) std.debug.print("state: {s}  ", .{@tagName(psp.state)});
    if (p_print) if (x.len < 50) {
        std.debug.print("token: {s}\n", .{x});
    } else {
        std.debug.print("token: {s}...\n", .{x[0..50]});
    };
    if (p_errcnt) if (psp.gp.errorcnt > 0) {
        std.debug.print("error count: {d}\n", .{psp.gp.errorcnt});
    };
    state: switch (psp.state) {
        .initialize => { // TODO: Probably just do this first yeah
            psp.prevrule = null;
            psp.preccounter = 0;
            psp.firstrule, psp.lastrule = .{ null, null };
            psp.gp.nrule = 0;
            continue :state .waiting_for_decl_or_rule;
        },
        .waiting_for_decl_or_rule => {
            if (x[0] == '%') {
                psp.state = .waiting_for_decl_keyword;
            } else if (isLower(x[0])) {
                psp.lhs = try Symbol_new(x);
                psp.nrhs = 0;
                psp.lhsalias = "";
                psp.state = .waiting_for_arrow;
            } else if (x[0] == '{') {
                if (psp.prevrule) |prev| {
                    if (prev.code.len != 0) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Code fragment beginning on this line is not the first " ++
                            "to follow the previous rule.", .{});
                        psp.errorcnt += 1;
                    } else if (strcmp(x, "{NEVER-REDUCE")) {
                        // Hidden feature!
                        prev.neverReduce = true;
                    } else {
                        prev.line = psp.tokenlineno;
                        prev.code = x[1..]; // Code lacks outer braces
                        prev.noCode = false;
                    }
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "There is no prior rule upon which to attach the code " ++
                        "fragment which begins on this line", .{});
                    psp.errorcnt += 1;
                }
            } else if (x[0] == '[') {
                psp.state = .precedence_mark_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Token {s} should be either \"%\" or a nonterminal name.", .{x});
                psp.errorcnt += 1;
            }
        },
        .precedence_mark_1 => {
            if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "The precedence symbol must be a terminal.", .{});
                psp.errorcnt += 1;
            } else if (psp.prevrule) |prev| {
                if (prev.precsym) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Precedence mark on this line is not the first " ++
                        "to follow the previous rule.", .{});
                    psp.errorcnt += 1;
                } else {
                    prev.precsym = try Symbol_new(x);
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "There is no prior rule to assign precedence \"{s}\".", .{x});
                psp.errorcnt += 1;
            }
            psp.state = .precedence_mark_2;
        },
        .precedence_mark_2 => {
            if (x[0] != ']') {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \"]\" on precedence mark.", .{});
                psp.errorcnt += 1;
            }
            psp.state = .waiting_for_decl_or_rule;
        },
        .waiting_for_arrow => {
            if (x.len >= 3 and x[0] == ':' and x[1] == ':' and x[2] == '=') {
                psp.state = .in_rhs;
            } else if (x[0] == '(') {
                psp.state = .lhs_alias_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Expected to see a \":\" following the LHS symbol \"%s\".", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_1 => {
            if (isAlpha(x[0])) {
                psp.lhsalias = x;
                psp.state = .lhs_alias_2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "\"%s\" is not a valid alias for the LHS \"%s\"\n", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_2 => {
            if (x[0] == ')') {
                psp.state = .lhs_alias_3;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \")\" following LHS alias name \"{s}\".", .{psp.lhsalias});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_3 => {
            if (x.len >= 3 and x[0] == ':' and x[1] == ':' and x[2] == '=') {
                psp.state = .in_rhs;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \"::=\" following: \"{s}({s})\".", //
                    .{ psp.lhs.name, psp.lhsalias });
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .in_rhs => {
            if (x[0] == '.') {
                // Note that the original code allocates one contiguous block of
                // bytes, doling them out to the three separate allocations below.
                // Not without regret, I am not, at this time, willing to follow suit.
                const rp = try Rule.create(psp.allocator);
                errdefer rp.destroy(psp.allocator);
                rp.ruleline = psp.tokenlineno;
                rp.rhs = try psp.allocator.alloc(*Symbol, psp.nrhs);
                rp.rhsalias = try psp.allocator.alloc([]const u8, psp.nrhs);
                for (0..psp.nrhs) |i| {
                    rp.rhs[i] = psp.rhs[i];
                    rp.rhsalias[i] = psp.alias[i];
                    if (rp.rhsalias[i].len > 0) rp.rhs[i].bContent = true;
                }
                rp.lhs = psp.lhs;
                rp.lhsalias = psp.lhsalias;
                rp.nrhs = psp.nrhs;
                rp.noCode = true;
                dbgassert(rp.precsym == null);
                rp.index = psp.gp.nrule;
                psp.gp.nrule += 1;
                rp.nextlhs = rp.lhs.rule;
                rp.lhs.rule = rp;
                dbgassert(rp.next == null);
                if (psp.firstrule == null) {
                    psp.firstrule = rp;
                    psp.lastrule = rp;
                } else { // Append to linked list
                    psp.lastrule.?.next = rp;
                    psp.lastrule = rp;
                }
                psp.prevrule = rp;
                psp.state = .waiting_for_decl_or_rule;
            } else if (isAlpha(x[0])) {
                if (psp.nrhs >= MAXRHS) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Too many symbols on RHS of rule beginning at \"{s}\".", .{x});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                } else {
                    psp.rhs[psp.nrhs] = try Symbol_new(x);
                    psp.alias[psp.nrhs] = "";
                    psp.nrhs += 1;
                }
            } else if ((x[0] == '|' or x[0] == '/') and psp.nrhs > 0 and x.len > 0 and isUpper(x[1])) {
                var msp = psp.rhs[psp.nrhs - 1];
                if (msp.type != .multiterminal) {
                    const origmsp = msp;
                    msp = try Symbol.create(psp.allocator, origmsp.name);
                    errdefer msp.destroy(psp.allocator);
                    msp.type = .multiterminal;
                    msp.nsubsym = 1;
                    msp.subsym = try psp.allocator.alloc(*Symbol, 1);
                    msp.subsym[0] = origmsp;
                    psp.rhs[psp.nrhs - 1] = msp;
                    // These go on a separate freelist
                    const fl = try psp.allocator.create(SymFreelist);
                    errdefer comptime unreachable;
                    fl.* = .{
                        .sp = msp,
                        .next = null,
                    };
                    if (sym_freelist) |free| {
                        fl.next = free;
                        sym_freelist = fl;
                    } else {
                        sym_freelist = fl;
                    }
                }
                msp.nsubsym += 1;
                msp.subsym = try psp.allocator.realloc(msp.subsym, msp.subsym.len + 1);
                // We know x[1] exists and is terminal-shaped, so this is valid:
                msp.subsym[msp.nsubsym - 1] = try Symbol_new(x[1..]);
                if (isLower(x[1]) or isLower(msp.subsym[0].name[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Cannot form a compound containing a non-terminal", .{});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                }
            } else if (x[0] == '(' and psp.nrhs > 0) {
                psp.state = .rhs_alias_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Illegal character on RHS of rule: \"{s}\".", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .rhs_alias_1 => {
            if (isAlpha(x[0])) {
                psp.alias[psp.nrhs - 1] = x;
                psp.state = .rhs_alias_2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "\"{s}\" is not a valid alias for the RHS symbol \"{s}\"\n", //
                    .{ x, psp.rhs[psp.nrhs - 1].name });
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .rhs_alias_2 => {
            if (x[0] == ')') {
                psp.state = .in_rhs;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \")\" following LHS alias name \"{s}\".", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .waiting_for_decl_keyword => {
            // This I'm doing with an enum, a StaticStringMap, and a switch.
            const decl = declarations.get(x) orelse {
                if (isAlpha(x[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Unknown declaration keyword: \"%{s}\".", .{x});
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Illegal declaration keyword: \"%{s}\".", .{x});
                }
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            };
            // Defaults:
            psp.declkeyword = x;
            psp.declargslot = null;
            psp.decllinenoslot = null;
            psp.insertLineMacro = true;
            psp.state = .waiting_for_decl_arg;
            switch (decl) {
                .name => {
                    psp.declargslot = &psp.gp.name;
                    psp.insertLineMacro = false;
                },
                .include => {
                    psp.declargslot = &psp.gp.include;
                },
                .code => {
                    psp.declargslot = &psp.gp.extracode;
                },
                .token_destructor => {
                    psp.declargslot = &psp.gp.tokendest;
                },
                .default_destructor => {
                    psp.declargslot = &psp.gp.vardest;
                },
                .token_prefix => {
                    psp.declargslot = &psp.gp.tokenprefix;
                    psp.insertLineMacro = false;
                },
                .syntax_error => {
                    psp.declargslot = &psp.gp.@"error";
                },
                .parse_accept => {
                    psp.declargslot = &psp.gp.accept;
                },
                .parse_failure => {
                    psp.declargslot = &psp.gp.failure;
                },
                .stack_overflow => {
                    psp.declargslot = &psp.gp.overflow;
                },
                .extra_argument => {
                    psp.declargslot = &psp.gp.arg;
                    psp.insertLineMacro = false;
                },
                .extra_context => {
                    psp.declargslot = &psp.gp.ctx;
                    psp.insertLineMacro = false;
                },
                .token_type => {
                    psp.declargslot = &psp.gp.tokentype;
                    psp.insertLineMacro = false;
                },
                .default_type => {
                    psp.declargslot = &psp.gp.vartype;
                    psp.insertLineMacro = false;
                },
                .realloc => {
                    psp.declargslot = &psp.gp.reallocFunc;
                    psp.insertLineMacro = false;
                },
                .free => {
                    psp.declargslot = &psp.gp.freeFunc;
                    psp.insertLineMacro = false;
                },
                .stack_size => {
                    psp.declargslot = &psp.gp.stacksize;
                    psp.insertLineMacro = false;
                },
                .start_symbol => {
                    psp.declargslot = &psp.gp.start;
                    psp.insertLineMacro = false;
                },
                .left => {
                    psp.preccounter += 1;
                    psp.declassoc = .left;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .right => {
                    psp.preccounter += 1;
                    psp.declassoc = .right;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .nonassoc => {
                    psp.preccounter += 1;
                    psp.declassoc = .none;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .destructor => {
                    psp.state = .waiting_for_destructor_symbol;
                },
                .type => {
                    psp.state = .waiting_for_datatype_symbol;
                },
                .fallback => {
                    psp.fallback = null;
                    psp.state = .waiting_for_fallback_id;
                },
                .token => {
                    psp.state = .waiting_for_token_name;
                },
                .wildcard => {
                    psp.state = .waiting_for_wildcard_id;
                },
                .token_class => {
                    psp.state = .waiting_for_class_id;
                },
            }
        },
        .waiting_for_destructor_symbol => {
            if (!isAlpha(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol name missing after %destructor keyword", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            }
            const sp = try Symbol_new(x);
            psp.declargslot = &sp.destructor;
            psp.decllinenoslot = &sp.destLineno;
            psp.insertLineMacro = true;
            psp.state = .waiting_for_decl_arg;
        },
        .waiting_for_datatype_symbol => {
            if (!isAlpha(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol name missing after %type keyword", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            }
            const sp = Symbol_find(x) orelse try Symbol_new(x);
            if (sp.datatype.len != 0) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol %type \"{s}\" already defined", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else {
                psp.declargslot = &sp.datatype;
                psp.insertLineMacro = false;
                psp.state = .waiting_for_decl_arg;
            }
        },
        .waiting_for_precedence_symbol => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (isUpper(x[0])) {
                const sp = try Symbol_new(x);
                if (sp.prec) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Symbol \"{s}\" has already be given a precedence.", .{x});
                    psp.errorcnt += 1;
                    // No new state assigned here (?)
                } else {
                    sp.prec = psp.preccounter;
                    sp.assoc = psp.declassoc;
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Can't assign a precedence to \"{s}\".", .{x});
                psp.errorcnt += 1;
            }
        },
        .waiting_for_decl_arg => {
            if (x[0] == '{' or x[0] == '"' or isAlnum(x[0])) {
                // NOTE: This is a difficult translation, because we eschew two
                // Cisms: the null sentinel, and (consequently) bare char *. So
                // idiomatic Zig looks quite different.
                var zBuffer: [50]u8 = undefined; // Line macro buffer
                // The code assumes declargslot is pointing at something, so null should be
                // unreachable here:
                const declargslot = psp.declargslot.?;
                const zOld: []const u8 = declargslot.*;
                const zNew = if (x[0] == '"' or x[0] == '{') x[1..] else x;
                var zLine: []u8 = zBuffer[0..0];
                // To build the new slice, we have to track bytes written:
                var zIdx: usize = 0;
                // The original code leaves some buffer here, because C
                // makes it difficult to count sprintf statements.  A problem
                // we do not have.
                var n = zOld.len + zNew.len;
                // Do we need a line macro?
                const addLineMacro = !psp.gp.nolineosflag and
                    psp.insertLineMacro and
                    psp.tokenlineno > 1 and
                    (psp.decllinenoslot == null or psp.decllinenoslot.?.* != 0);
                if (addLineMacro) {
                    var nBack = std.mem.count(u8, psp.filename, "\\");
                    nBack += std.mem.count(u8, psp.filename, "\"");
                    zLine = std.fmt.bufPrint(&zBuffer, "#line {d} ", .{psp.tokenlineno}) catch |err| slice: {
                        // Should be literally impossible but ¯\_(ツ)_/¯
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Buffer overflow on #line directive print: {s}", .{@errorName(err)});
                        psp.errorcnt += 1;
                        break :slice zBuffer[0..0];
                    }; // 3 for ", ", \n:
                    n += zLine.len + psp.filename.len + nBack + 3;
                }
                // We put this back on declargslot and PSP once we know how long the
                // slice actually should be.
                const zBuf = try psp.allocator.realloc(declargslot.*, n);
                @memcpy(zBuf[0..zOld.len], zOld);
                zIdx += zOld.len;
                if (addLineMacro) {
                    // TODO: there's no reason to do this repeatedly for every loop,
                    // the file name is not going to change.  This should be
                    // calculated once on load and the value put on gp, *Lemon.
                    if (zIdx > 0 and zBuf[zIdx - 1] != '\n') {
                        zBuf[zIdx] = '\n';
                        zIdx += 1;
                    }
                    @memcpy(zBuf[zIdx..][0..zLine.len], zLine);
                    zIdx += zLine.len + 1;
                    zBuf[zIdx - 1] = '"';
                    for (0..psp.filename.len) |i| {
                        if (psp.filename[i] == '\\' or psp.filename[i] == '"') {
                            zBuf[zIdx] = '\\';
                            zIdx += 1;
                        }
                        zBuf[zIdx] = psp.filename[i];
                        zIdx += 1;
                    }
                    zBuf[zIdx] = '"';
                    zBuf[zIdx + 1] = '\n';
                    zIdx += 2;
                }
                if (psp.decllinenoslot) |linenoslot| if (linenoslot.* == 0) {
                    psp.decllinenoslot.?.* = @intCast(psp.tokenlineno);
                };
                @memcpy(zBuf[zIdx..][0..zNew.len], zNew);
                zIdx += zNew.len;
                // Finally, we put it all where it's pointed:
                declargslot.* = zBuf;
                dbgassert(zIdx == zBuf.len);
                dbgassert(psp.declargslot == declargslot);
                psp.state = .waiting_for_decl_or_rule;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Illegal argument to %{s}: {s}", .{ psp.declkeyword, x });
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            }
        },
        .waiting_for_fallback_id => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%fallback argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
                // TODO: no resync here, is that right?
            } else {
                const sp = try Symbol_new(x);
                if (psp.fallback == null) {
                    psp.fallback = sp;
                } else if (sp.fallback != null) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "More than one fallback assigned to token {s}", .{sp.name});
                    psp.errorcnt += 1;
                    // TODO: no resync here, is that right?
                } else {
                    sp.fallback = psp.fallback;
                    psp.gp.has_fallback = true;
                }
            }
        },
        .waiting_for_token_name => {
            // Tokens do not have to be declared before use.  But they can be
            // in order to control their assigned integer number.  The number for
            // each token is assigned when it is first seen.  So by including
            //
            //     %token ONE TWO THREE.
            //
            // early in the grammar file, that assigns small consecutive values
            // to each of the tokens ONE TWO and THREE.
            //
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
            } else {
                _ = try Symbol_new(x);
            }
        },
        .waiting_for_wildcard_id => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%wildcard argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
            } else {
                const sp = try Symbol_new(x);
                if (psp.gp.wildcard == null) {
                    psp.gp.wildcard = sp;
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Extra wildcard to token: {s}", .{x});
                    psp.errorcnt += 1;
                }
            }
        },
        .waiting_for_class_id => {
            if (!isLower(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token_class must be followed by an identifier: {s}", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else if (Symbol_find(x)) |_| {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol \"{s}\" already used", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else {
                psp.tkclass = try Symbol_new(x);
                psp.tkclass.type = .multiterminal;
                psp.state = .waiting_for_class_token;
            }
        },
        .waiting_for_class_token => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (isUpper(x[0]) or ((x[0] == '|' or x[0] == '/') and isUpper(x[1]))) {
                const msp = psp.tkclass;
                msp.nsubsym += 1;
                msp.subsym = subsym: {
                    if (msp.subsym.len == 0)
                        break :subsym try psp.allocator.alloc(*Symbol, 1)
                    else
                        break :subsym try psp.allocator.realloc(msp.subsym, msp.nsubsym);
                };
                msp.subsym[msp.nsubsym - 1] = try Symbol_new(if (!isUpper(x[0])) x else x[1..]);
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token_class argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            }
        },
        // TODO: These don't need to be separate states
        .resync_after_rule_error,
        .resync_after_decl_error,
        => {
            if (x[0] == '.') psp.state = .waiting_for_decl_or_rule;
            if (x[0] == '%') psp.state = .waiting_for_decl_keyword;
        },
    }
}

const Declaration = enum {
    name,
    include,
    code,
    token_destructor,
    default_destructor,
    token_prefix,
    syntax_error,
    parse_accept,
    parse_failure,
    stack_overflow,
    extra_argument,
    extra_context,
    token_type,
    default_type,
    realloc,
    free,
    stack_size,
    start_symbol,
    left,
    right,
    nonassoc,
    destructor,
    type,
    fallback,
    token,
    wildcard,
    token_class,
};

const directive_list = [_]struct { []const u8, Declaration }{
    .{ "name", .name },
    .{ "include", .include },
    .{ "code", .code },
    .{ "token_destructor", .token_destructor },
    .{ "default_destructor", .default_destructor },
    .{ "token_prefix", .token_prefix },
    .{ "syntax_error", .syntax_error },
    .{ "parse_accept", .parse_accept },
    .{ "parse_failure", .parse_failure },
    .{ "stack_overflow", .stack_overflow },
    .{ "extra_argument", .extra_argument },
    .{ "extra_context", .extra_context },
    .{ "token_type", .token_type },
    .{ "default_type", .default_type },
    .{ "realloc", .realloc },
    .{ "free", .free },
    .{ "stack_size", .stack_size },
    .{ "start_symbol", .start_symbol },
    .{ "left", .left },
    .{ "right", .right },
    .{ "nonassoc", .nonassoc },
    .{ "destructor", .destructor },
    .{ "type", .type },
    .{ "fallback", .fallback },
    .{ "token", .token },
    .{ "wildcard", .wildcard },
    .{ "token_class", .token_class },
};

const declarations = std.StaticStringMap(Declaration).initComptime(directive_list);

/// Lemon puts the scanner loop in `Parse`, I prefer it separate.
fn scan(ps: *PState, fb: [:0]const u8) !void {
    var i: usize = 0;
    var lineno: usize = 1;
    scanning: while (i < fb.len) {
        var skip: bool = false; // True when we advance one more before loop
        if (fb[i] == '\n') lineno += 1;
        if (isSpace(fb[i])) {
            i += 1;
            continue :scanning;
        } // Skip all whitespace
        // Skip C++ style comments
        if (fb[i] == '/' and fb[i + 1] == '/') {
            i += 2;
            while (fb[i] != '\n' and fb[i] != 0) : (i += 1) {}
            if (fb[i] != 0) {
                if (fb[i] == '\n') lineno += 1;
                i += 1;
                continue :scanning;
            } else break :scanning;
        }
        // Skip C style comments
        if (fb[i] == '/' and fb[i + 1] == '*') {
            i += 2;
            if (fb[i] != 0) break :scanning;
            if (fb[i] == '*') i += 1;
            if (fb[i] != 0) break :scanning;
            while (fb[i] != 0 and (fb[i] != '/' or fb[i - 1] != '*')) : (i += 1) {
                if (fb[i] == '\n') lineno += 1;
            }
            i += 1;
            if (fb[i] != 0) continue :scanning;
        }
        if (p_print) std.debug.print("tstart == {d} '{u}' ", .{ i, fb[i] });
        ps.tokenstart = i; // Mark the beginning of the token
        ps.tokenlineno = lineno; // Linenumber on which token begins
        if (fb[i] == '"') { // String literals
            i += 1;
            while (fb[i] != 0 and fb[i] != '"') : (i += 1) {
                if (fb[i] == '\n') lineno += 1;
            }
            if (fb[i] == 0) {
                ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                    "String starting on this line is not terminated before " ++
                    "the end of the file.", .{});
                ps.errorcnt += 1;
                break :scanning;
            } else {
                skip = true;
            }
        } else if (fb[i] == '{') { // A block of C code
            var level: usize = 1;
            i += 1;
            while (fb[i] != 0 and (level > 1 or fb[i] != '}')) : (i += 1) {
                if (fb[i] == '\n') lineno += 1 //
                else if (fb[i] == '{') level += 1 //
                else if (fb[i] == '}') level -= 1 //
                else if (fb[i] == '/' and i + 1 < fb.len and fb[i + 1] == '*') {
                    // Skip C comments
                    i += 2;
                    var prev: u8 = 0;
                    while (fb[i] != 0 and (fb[i] != '/' or prev != '*')) : (i += 1) {
                        if (fb[i] == '\n') lineno += 1;
                        prev = fb[i];
                    }
                } else if (fb[i] == '/' and fb[i + 1] == '/') {
                    // Skip C++ comments too
                    i += 2;
                    while (fb[i] != 0 and fb[i] != '\n') : (i += 1) {}
                } else if (fb[i] == '"' or fb[i] == '\'') {
                    // String or character literals (since the latter can have " in it)
                    const startchar = fb[i];
                    var prevc: u8 = 0;
                    i += 1;
                    while (fb[i] != 0 and (fb[i] != startchar or prevc == '\\')) : (i += 1) {
                        if (fb[i] == '\n') lineno += 1;
                        if (prevc == '\\')
                            prevc = 0
                        else
                            prevc = fb[i]; // clever
                    }
                }
            }
            if (i == fb.len and fb[i - 1] != '}') {
                ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                    "C code starting on this line is not terminated before " ++
                    "the end of the file.", .{});
                ps.errorcnt += 1;
            } else {
                skip = true; // Clip end of C blocks also
            }
        } else if (isAlnum(fb[i])) {
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else if (i + 2 < fb.len and fb[i] == ':' and fb[i + 1] == ':' and fb[i + 2] == '=') {
            i += 3;
        } else if (fb[i] == '/' or fb[i] == '|' and isAlpha(fb[i + 1])) {
            i += 2;
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else { //  All other (one character) operators
            i += 1;
        }
        const x = fb[ps.tokenstart..i];
        if (p_print) std.debug.print("i == {d} '{u}' ", .{ i, fb[i] });
        try parseonetoken(ps, x);
        if (p_print) std.debug.print("skip: {any} ", .{skip});
        if (skip) i += 1; // End byte of string and code tokens.
    }
}

/// Reduce the size of the action tables, if possible, by making use
/// of defaults.
///
/// In this version, we take the most frequent REDUCE action and make
/// it the default.  Except, there is no default if the wildcard token
/// is a possible look-ahead.
fn CompressTables(lemp: *Lemon) !void {
    states: for (lemp.sorted) |stp| {
        var nbest: usize = 0;
        var rbest: ?*Rule = null;
        var usesWildcard = false;
        var m_ap: ?*Action = stp.ap;
        actions: while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .shift and ap.sp == lemp.wildcard) {
                usesWildcard = true;
            }
            if (ap.type != .reduce) continue :actions;
            const rp = ap.x.rp.?; // Always rule on .reduce
            if (rp.lhsStart) continue :actions;
            if (rp == rbest) continue :actions;
            var n: usize = 1;
            var m_ap2 = ap.next;
            next_act: while (m_ap2) |ap2| : (m_ap2 = ap2.next) {
                if (ap2.type != .reduce) continue :next_act;
                const rp2 = ap2.x.rp.?;
                if (rp2 == rbest) continue :next_act;
                if (rp2 == rp) n += 1;
            }
            if (n > nbest) {
                nbest = n;
                rbest = rp;
            }
            // Do not make a default if the number of rules to default
            // is not at least 1 or if the wildcard token is a possible
            // lookahead.
            //
        }
        if (nbest < 1 or usesWildcard) continue :states;
        // Combine matching REDUCE actions into a single default.
        m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce and ap.x.rp == rbest) break;
        }
        dbgassert(m_ap != null);
        m_ap.?.sp = try Symbol_new("{default}");
        m_ap = m_ap.?.next;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce and ap.x.rp == rbest) {
                ap.type = .not_used;
            }
        }
        stp.ap = if (stp.ap) |ap| Action.sort(ap) else null;
        m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .shift) break;
            if (ap.type == .reduce and ap.x.rp != rbest) break;
        } else {
            stp.autoreduce = true;
            stp.pDefltReduce = rbest;
        }
    }
    // Make a second pass over all states and actions.  Convert
    // every action that is a SHIFT to an autoReduce state into
    // a SHIFTREDUCE action.
    for (lemp.sorted) |stp| {
        var m_ap: ?*Action = stp.ap;
        actions: while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type != .shift) continue :actions;
            const pNextState = ap.x.stp;
            if (pNextState.autoreduce and pNextState.pDefltReduce != null) {
                ap.type = .shiftreduce;
                ap.x = .{ .rp = pNextState.pDefltReduce };
            }
        }
    }
    // If a SHIFTREDUCE action specifies a rule that has a single RHS term
    // (meaning that the SHIFTREDUCE will land back in the state where it
    // started) and if there is no C-code associated with the reduce action,
    // then we can go ahead and convert the action to be the same as the
    // action for the RHS of the rule.
    //
    // TODO: do_not_optimize_terminals
    for (lemp.sorted) |stp| {
        var m_ap: ?*Action = stp.ap;
        var nextap: ?*Action = null;
        actions: while (m_ap) |ap| : (m_ap = nextap) {
            nextap = ap.next;
            if (ap.type != .shiftreduce) continue :actions;
            const rp = ap.x.rp.?;
            if (!rp.noCode) continue :actions;
            if (rp.rhs.len != 1) continue :actions;
            if (comptime do_not_optimize_terminals) {
                // Only apply this optimization to non-terminals.  It would be OK to
                // apply it to terminal symbols too, but that makes the parser tables
                // larger.
                if (ap.sp.index < lemp.nterminal) continue :actions;
            }
            // If we reach this point, it means the optimization can be applied
            nextap = ap;
            var m_ap2 = stp.ap;
            while (m_ap2 != null and
                (m_ap2 == ap or m_ap2.?.sp != rp.lhs)) : (m_ap2 = m_ap2.?.next)
            {}
            dbgassert(m_ap2 != null);
            const ap2 = m_ap2.?;
            ap.spOpt = ap2.sp;
            ap.type = ap2.type;
            ap.x = ap2.x;
        }
    }
}

//
// Compare two states for sorting purposes.  The smaller state is the
// one with the most non-terminal actions.  If they have the same number
// of non-terminal actions, then the smaller is the one with the most
// token actions.
fn stateResortCompare(_: void, pA: *State, pB: *State) bool {
    if (pA.nNtAct > pB.nNtAct) return true;
    if (pA.nNtAct < pB.nNtAct) return false;
    if (pA.nTknAct > pB.nTknAct) return true;
    if (pA.nTknAct < pB.nTknAct) return false;
    if (pA.statenum > pB.statenum) return true;
    if (pA.statenum < pB.statenum) return false;
    unreachable;
}

//
// Renumber and resort states so that states with fewer choices
// occur at the end.  Except, keep state 0 as the first state.
//
fn ResortStates(lemp: *Lemon) void {
    for (lemp.sorted) |stp| {
        if (p_check1) {
            dprint("state before resort: {d}\n", .{stp.statenum});
        }
        stp.nTknAct = 0;
        stp.nNtAct = 0;
        // TODO: probably a null here yeah
        stp.iDfltReduce = -1; //  Init dflt action to "syntax error"
        stp.iTnkOfst = null;
        stp.iNtOfst = null;
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            const m_iAction = compute_action(lemp, ap);
            if (m_iAction) |iAction| {
                if (ap.sp.index < lemp.nterminal) {
                    stp.nTknAct += 1;
                } else if (ap.sp.index < lemp.nsymbol) {
                    stp.nNtAct += 1;
                } else {
                    dbgassert(!stp.autoreduce or stp.pDefltReduce == ap.x.rp);
                    stp.iDfltReduce = @intCast(iAction);
                }
            }
        }
    }
    std.mem.sort(*State, lemp.sorted[1..], {}, stateResortCompare);
    for (lemp.sorted, 0..) |stp, i| {
        if (p_check1) {
            dprint("statenum was #{d}, now #{d}\n", .{ stp.statenum, i });
        }
        stp.statenum = @intCast(i);
    }
    lemp.nxstate = lemp.nstate;
    while (lemp.nxstate > 1 and lemp.sorted[lemp.nxstate - 1].autoreduce) {
        lemp.nxstate -= 1;
    }
}

// Given an action, compute the integer value for that action
// which is to be put in the action table of the generated machine.
// Return negative if no action should be generated.
fn compute_action(lemp: *Lemon, ap: *Action) ?u32 {
    return act: switch (ap.type) {
        .shift => break :act ap.x.stp.statenum,
        .shiftreduce => {
            // Since a SHIFT is inherent after a prior REDUCE, convert any
            // SHIFTREDUCE action with a nonterminal on the LHS into a simple
            // REDUCE action:
            if (ap.sp.index >= lemp.nterminal and
                (lemp.errsym == null or ap.sp.index != lemp.errsym.?.index))
            {
                break :act lemp.minReduce + ap.x.rp.?.iRule;
            } else {
                break :act lemp.minShiftReduce + ap.x.rp.?.iRule;
            }
        },
        .reduce => break :act lemp.minReduce + ap.x.rp.?.iRule,
        .@"error" => break :act lemp.errAction,
        .accept => break :act lemp.accAction,
        else => break :act null,
    };
}
// PRIVATE int compute_action(struct lemon *lemp, struct action *ap)
// {
//   int act;
//   switch( ap->type ){
//     case SHIFT:  act = ap->x.stp->statenum;                        break;
//     case SHIFTREDUCE: {
//       /* Since a SHIFT is inherent after a prior REDUCE, convert any
//       ** SHIFTREDUCE action with a nonterminal on the LHS into a simple
//       ** REDUCE action: */
//       if( ap->sp->index>=lemp->nterminal
//        && (lemp->errsym==0 || ap->sp->index!=lemp->errsym->index)
//       ){
//         act = lemp->minReduce + ap->x.rp->iRule;
//       }else{
//         act = lemp->minShiftReduce + ap->x.rp->iRule;
//       }
//       break;
//     }
//     case REDUCE: act = lemp->minReduce + ap->x.rp->iRule;          break;
//     case ERROR:  act = lemp->errAction;                            break;
//     case ACCEPT: act = lemp->accAction;                            break;
//     default:     act = -1; break;
//   }
//   return act;
// }

//| [5230] Set manipulation
//|
//| This is actually pretty straightforward, we use a []bool instead of a
//| *char but same same.  It can probably be refined later but honestly
//| space efficiency is not a big deal (in that I DEFINITELY DO NOT need
//| to beat lemon.c there), and byte booleans are going to be faster than
//| bitsets, if anything.  Then again, I would get union for free, not that
//| it's an especially recondite algorithm...

threadlocal var set_size: usize = 0;

fn SetSize(n: usize) void {
    set_size = n + 1;
}

//| SetNew is just allocating []bool, SetFree needs the allocator so we
//| take care of it when destroying things with sets on them.

// Add a new element to the set.  Return `true` if the element was added
// and `false` if it was already there.
fn SetAdd(set: []bool, n: usize) bool {
    const was = set[n];
    assert(n < set_size);
    set[n] = true;
    return !was;
}

/// Add every element of s2 to s1.  Return `true` if s1 changes.
fn SetUnion(s1: []bool, s2: []bool) bool {
    assert(s1.len == s2.len);
    var changed = false;
    for (0..s1.len) |i| {
        if (!s2[i]) continue;
        if (!s1[i]) {
            changed = true;
            s1[i] = true;
        }
    }
    return changed;
}

pub fn main() !void {
    // We begin, as always, with the Allocator Dance
    var dbga: std.heap.DebugAllocator(.{}) = .init;
    defer {
        assert(.ok == dbga.deinit());
    }
    // TODO: Use dbga for debug builds and page otherwise, use smp (?!)
    // for not-pools.

    // Set up pools.
    const allocator = dbga.allocator();
    action_allocator = ActionAllocator.init(std.heap.page_allocator);
    defer action_allocator.deinit();
    Configlist_init(allocator, .init(std.heap.page_allocator));
    defer {
        Configlist_reset();
    }
    cf_ls.allocator = allocator;
    plink_freelist = .init(std.heap.page_allocator);
    is_plink_freelist = true;
    defer {
        plink_freelist.deinit();
        is_plink_freelist = false;
    }
    try plink_freelist.preheat(100);
    Strsafe_init(allocator);
    defer Strsafe_free();
    Symbol_init(allocator);
    defer Symbol_free();
    try State_init(allocator);
    defer State_free();

    defer {
        // Some rare symbols 'spill', because they can't be
        // stored in the Symbol intern map, we we free those
        // here.
        while (sym_freelist) |free| {
            free.sp.destroy(allocator);
            sym_freelist = free.next;
            allocator.destroy(free);
        }
    }

    // These need to exist so that some later argument parser can
    // assign them.  That that point of course, variable, but one
    // damn thing at a damn time.
    const version = true;
    const rpflag = true;
    const basisflag = true;
    const compress = true;
    const quiet = false;
    const statistics = true;
    const mhflag = true;
    const nolinenosflag = true;
    const noResort = false;
    const sqlFlag = true;
    const printPP = false;
    // Reconcile Zig to this unfortunate situation:
    _ = .{ version, rpflag, basisflag, compress, quiet, statistics, mhflag, nolinenosflag, noResort, sqlFlag, printPP };

    const args = try std.process.argsAlloc(allocator);
    // TODO: Quirk-compatible flags parser.  Do this last-ish.
    // [1636-1689] - todo
    defer std.process.argsFree(allocator, args);
    const filename: []const u8 = file: {
        if (args.len >= 1) {
            break :file args[1];
        } else {
            std.debug.print("lemon.zig needs a filename\n", .{});
            std.process.exit(1);
        }
    };
    var lem = try Lemon.create(allocator);
    defer lem.destroy(allocator);
    lem.argv = args;
    lem.filename = filename;
    lem.basisflag = basisflag;
    lem.nolineosflag = nolinenosflag;
    lem.printPreprocessed = printPP;
    _ = try Symbol_new("$"); // Why?
    // TODO: Write a full parse file and move the file opening stuff there,
    // with the Pstate, etc.
    var pstate = try PState.create(allocator, lem);
    defer pstate.destroy();
    pstate.gp = lem;
    pstate.filename = filename;

    try Parse(pstate);
    if (lem.printPreprocessed or lem.errorcnt > 0) {
        logger.err("exiting due to preprocess only or too many errors", .{});
        exit(@truncate(lem.errorcnt));
    }
    if (lem.nrule == 0) {
        logger.err("Empty grammar.", .{});
        exit(1);
    }
    lem.errsym = Symbol_find("error");

    // Count and index the symbols of the grammar
    _ = try Symbol_new("{default}");
    lem.symbols = Symbol_arrayof();
    sort(*Symbol, lem.symbols, {}, Symbol_lessThanFn);
    if (p_symbols) for (lem.symbols) |symbol| {
        std.debug.print("{s} ", .{symbol.name});
    };
    for (lem.symbols, 0..) |sym, i| {
        sym.index = @intCast(i);
    }
    {
        var i: usize = lem.symbols.len;
        while (lem.symbols[i - 1].type == .multiterminal) : (i -= 1) {}
        dbgassert(strcmp(lem.symbols[i - 1].name, "{default}"));
        lem.nsymbol = i - 1;
        i = 1;
        while (isUpper(lem.symbols[i].name[0])) : (i += 1) {}
        lem.nterminal = i;
    }
    sequenceRules(lem);
    // [1726]
    // /* Generate a reprint of the grammar, if requested on the command line */
    // else
    //
    SetSize(lem.nterminal + 1);
    // Find the precedence for every production rule (that has one)
    FindRulePrecedences(lem);
    if (p_check1 or p_symbols) {
        dprint("Sorted rules: {s}\n", .{lem.filename});
        var rp: ?*Rule = lem.rule;
        while (rp) |rule| : (rp = rule.next) {
            dprint("{s} ({d})  ", .{ rule.lhs.name, rule.iRule });
        }
        dprint("\n", .{});
    }
    // Compute the lambda-nonterminals and the first-sets for every
    // nonterminal
    try FindFirstSets(lem);
    if (p_check1) {
        var rp: ?*Rule = lem.rule;
        while (rp) |rule| : (rp = rule.next) {
            const s1 = rule.lhs;
            dprint("lhs: {s} ({d})", .{ s1.name, s1.index });
            if (s1.lambda) {
                dprint(" LAMBDA ", .{});
            }
            for (s1.firstset) |b| {
                if (b) {
                    dprint("+", .{});
                } else {
                    dprint(".", .{});
                }
            }
            dprint("\n", .{});
            dbgassert(rule.rhs.len == rule.nrhs);
            for (rule.rhs, 0..) |s2, i| {
                dprint("  {d}:{s} ({d})\n", .{ i, s2.name, s2.index });
            }
        }
    }
    dbgassert(lem.nstate == 0);
    // Compute all LR(0) states.  Also record follow-set propagation
    // links so that the follow-set can be computed later
    try FindStates(lem);
    lem.sorted = State_arrayof();
    dbgassert(lem.sorted.len == lem.nstate);
    if (p_check1) {
        for (lem.sorted, 0..) |stp, i| {
            dprint("State {d} #{d}: ", .{ i, stp.statenum });
            if (stp.bp) |bp| {
                dprint("{s}", .{bp.rp.lhs.name});
            } else {
                dprint("(null)", .{});
            }
            dprint("\n", .{});
        }
    }
    // /* Tie up loose ends on the propagation links */
    try FindLinks(lem);
    if (p_check1) {
        for (lem.sorted) |stp| {
            var maybe_cfp: ?*Config = stp.cfp;
            while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
                dprint("cfp: {s}:{d} fplp count: ", .{ cfp.rp.lhs.name, cfp.rp.index });
                var plp_count: usize = 0;
                var maybe_plp: ?*PLink = cfp.fplp;
                while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                    plp_count += 1;
                }
                dprint("{d}\n", .{plp_count});
            }
        }
    }
    // Compute the follow set of every reducible configuration
    FindFollowSets(lem);

    // Compute the action tables
    try FindActions(lem);
    // Compress the action tables
    if (compress) try CompressTables(lem);
    // Reorder and renumber the states so that states with fewer choices
    // occur at the end.  This is an optimization that helps make the
    // generated parser tables smaller.
    if (!noResort) ResortStates(lem);
    // Generate a report of the parser generated.  (the "y.output" file)
    if (!quiet) try ReportOutput(lem);
    { // This is the bulk of the remaining work:
        // /* Reorder and renumber the states so that states with fewer choices
        // ** occur at the end.  This is an optimization that helps make the
        // ** generated parser tables smaller. */
        // if( noResort==0 ) ResortStates(&lem);
        //
        // /* Generate a report of the parser generated.  (the "y.output" file) */
        // if( !quiet ) ReportOutput(&lem);
        //
        // /* Generate the source code for the parser */
        // ReportTable(&lem, mhflag, sqlFlag);
        //
        // /* Produce a header file for use by the scanner.  (This step is
        // ** omitted if the "-m" option is used because makeheaders will
        // ** generate the file for us.) */
        // if( !mhflag ) ReportHeader(&lem);
    }
    // The finale looks like this:
    //
    // if( statistics ){
    //   printf("Parser statistics:\n");
    //   stats_line("terminal symbols", lem.nterminal);
    //   stats_line("non-terminal symbols", lem.nsymbol - lem.nterminal);
    //   stats_line("total symbols", lem.nsymbol);
    //   stats_line("rules", lem.nrule);
    //   stats_line("states", lem.nxstate);
    //   stats_line("conflicts", lem.nconflict);
    //   stats_line("action table entries", lem.nactiontab);
    //   stats_line("lookahead table entries", lem.nlookaheadtab);
    //   stats_line("total table size (bytes)", lem.tablesize);
    // }
    // if( lem.nconflict > 0 ){
    //   fprintf(stderr,"%d parsing conflicts.\n",lem.nconflict);
    // }
    //
    // /* return 0 on success, 1 on failure. */
    // exitcode = ((lem.errorcnt > 0) || (lem.nconflict > 0)) ? 1 : 0;
    // exit(exitcode);
    // return (exitcode);
    //
    // Which is adequately straightforward imho.
    //
    //std.process.cleanExit();
    std.process.exit(0);
}

//| [1809] MergeSort
//|
//| This will be the sharpest deviation from Lemon.  Although the technique
//| used to achieve a type-generic merge sort is feasible in Zig (and is
//| very clever), we're better off returning a brace of functions, given the
//| type information we need.
//|
//| We take the type, the name of the field pointing to the next item in the
//| list, and a compare function which returns true if a is `<=` b.  The
//| equality tie-breaker is important, because it gives us sort stability.
//|
//| We then specialize the functions accordingly, returning the one we need.
//|
//| NOTE: to self: when you port this to Zelda, use std.math.Order, so we
//| can add sorts in both directions and they'll both be stable.

const LISTSIZE = 32;

fn mergeSortFn(
    T: type,
    comptime next: []const u8,
    lteFn: fn (a: *T, b: *T) bool,
) fn (*T) *T {
    return struct {
        /// Takes a pointer to *T, the head of a linked list found with
        /// t.next.  Merge sorts the list, returning a pointer to the
        /// head of a sorted list containing the elements of the passed-
        /// in list.
        pub fn msort(a: *T) *T {
            var ep: ?*T = null;
            var set: [LISTSIZE]?*T = .{null} ** LISTSIZE;
            var maybe_list: ?*T = a;
            var before: usize = 0;
            if (is_debug) {
                while (maybe_list) |list| : (maybe_list = @field(list, next)) {
                    before += 1;
                }
                maybe_list = a;
            }
            while (maybe_list) |list| {
                ep = list;
                maybe_list = @field(list, next);
                @field(ep.?, next) = null;
                var i: usize = 0;
                while (i < LISTSIZE - 1 and set[i] != null) : (i += 1) {
                    ep = merge(ep, set[i]);
                    set[i] = null;
                }
                if (i == LISTSIZE) i -= 1;
                set[i] = ep;
            }

            ep = null;
            for (0..LISTSIZE) |i| {
                if (set[i]) |tail| {
                    ep = merge(tail, ep);
                }
            }
            var after: usize = 0;
            if (is_debug) {
                var maybe_ep = ep;
                while (maybe_ep) |list| : (maybe_ep = @field(list, next)) {
                    after += 1;
                }
                if (before != after) {
                    std.debug.panic("list: before {d}, after {d}", .{ before, after });
                }
            }
            return ep.?;
        }

        // Merge two linked lists, given the head. Either the first or the
        // second may be null: by construction, they will never both be
        // null, but it's harmless to our purposes to return a `?*T`, so
        // we wouldn't benefit from that fact and don't take advantage of it.
        fn merge(maybe_a: ?*T, maybe_b: ?*T) ?*T {
            if (maybe_a == null) return maybe_b;
            if (maybe_b == null) return maybe_a;
            var a: ?*T = maybe_a;
            var b: ?*T = maybe_b;
            const head: *T = if (lteFn(a.?, b.?)) head: {
                const h = a.?;
                a = @field(h, next);
                break :head h;
            } else head: {
                const h = b.?;
                b = @field(h, next);
                break :head h;
            };
            var ptr: *T = head;
            while (a != null and b != null) {
                const a_ptr = a.?;
                const b_ptr = b.?;
                if (lteFn(a_ptr, b_ptr)) {
                    @field(ptr, next) = a_ptr;
                    ptr = a_ptr;
                    a = @field(a_ptr, next);
                } else {
                    @field(ptr, next) = b_ptr;
                    ptr = b_ptr;
                    b = @field(b_ptr, next);
                }
            }
            if (a) |a_ptr| {
                @field(ptr, next) = a_ptr;
            } else {
                @field(ptr, next) = b;
            }
            return head;
        }
    }.msort;
}

fn sequenceRules(lem: *Lemon) void {
    // Assign sequential rule numbers.  Start with 0.  Put rules that have no
    // reduce action C-code associated with them last, so that the switch()
    // statement that selects reduction actions will have a smaller jump table.
    // NOTE: the original code does all this assigning, then sorts. I don't
    // see why, since we create the order right here.  We can just:
    var rnum: usize = 0;
    var rp: ?*Rule = lem.rule;
    var action_head: ?*Rule = null;
    var action_tail: ?*Rule = null;
    var no_act_head: ?*Rule = null;
    var no_act_tail: ?*Rule = null;
    while (rp) |rule| : (rp = rule.next) {
        if (rule.code.len > 0) {
            rule.iRule = @intCast(rnum);
            rnum += 1;
            if (action_head == null) {
                action_head = rule;
                action_tail = rule;
            } else {
                // By the above, we have the action
                // tail, so
                action_tail.?.next = rule;
                action_tail = rule;
            }
        } else {
            if (no_act_head == null) {
                no_act_head = rule;
                no_act_tail = rule;
            } else {
                no_act_tail.?.next = rule;
                no_act_tail = rule;
            }
        }
    } // Cut the tails:
    if (action_tail) |act_tail| act_tail.next = null;
    if (no_act_tail) |no_act| no_act.next = null;
    lem.nruleWithAction = rnum;
    rp = no_act_head; // This works correctly even if there are no no-action rules
    while (rp) |rule| : (rp = rule.next) {
        dbgassert(rule.code.len == 0);
        rule.iRule = @intCast(rnum);
        rnum += 1;
    }
    lem.startRule = lem.rule;
    // We must have at least one rule, or we bailed already, so this works too:
    lem.rule = if (action_head) |act_head| act_head else no_act_head.?;
    if (action_head) |_| {
        // Means we have an action_tail too:
        action_tail.?.next = no_act_head;
        dbgassert(no_act_tail != null and no_act_tail.?.next == null);
    } // Sorted!
    rp = lem.startRule;
    if (builtin.mode == .Debug) while (rp) |rule| : (rp = rule.next) {
        if (rule.next) |next| {
            dbgassert(rule.iRule + 1 == next.iRule);
        }
    };
}

//| Global State
//
// lemon.c uses some judicious static globals, and if only to
// ease porting, lemon.zig does likewise.
//
// I will want to 'modularize' zitron, so that it can be, in
// particular, compiled to WASM and run in the browser.  But
// that can wait.  I might even give lemon.zig the same
// treatment for the same reason, I really don't know enough
// about WASM to say if that would even help.  I'm sure I've
// seen "programs" which would have a main function running
// in the browser, so surely there's an affordance for it.

threadlocal var str_safe: StrSafe = undefined;
threadlocal var is_a_strsafe: bool = false;

const StrSafe = struct {
    safe: StringArrayHashMap(void),
    allocator: Allocator,

    pub fn init(allocator: Allocator) StrSafe {
        return .{ .allocator = allocator, .safe = .empty };
    }

    pub fn find(strsafe: *StrSafe, key: []const u8) ?[]const u8 {
        return strsafe.safe.getKey(key);
    }

    pub fn intern(strsafe: *StrSafe, k: []const u8) ![]const u8 {
        if (strsafe.safe.getKey(k)) |key| {
            return key;
        }
        const dupe = try strsafe.allocator.dupe(u8, k);
        try strsafe.safe.put(strsafe.allocator, dupe, {});
        return dupe;
    }
};

fn Strsafe_init(allocator: Allocator) void {
    if (is_a_strsafe) return; // I don't think this happens..
    defer is_a_strsafe = true;
    str_safe = .init(allocator);
}

fn Strsafe(data: []const u8) ![]const u8 {
    dbgassert(is_a_strsafe);
    return str_safe.intern(data);
}

fn Strsafe_find(key: []const u8) ?[]const u8 {
    dbgassert(is_a_strsafe);
    return str_safe.find(key);
}

fn Strsafe_free() void {
    dbgassert(is_a_strsafe);
    defer is_a_strsafe = false;
    // strsafe owns all interned strings:
    for (str_safe.safe.keys()) |str| {
        str_safe.allocator.free(str);
    }
    str_safe.safe.deinit(str_safe.allocator);
}

//| Symbols
//|

const SymbolSafe = struct {
    safe: StringArrayHashMap(*Symbol),
    allocator: Allocator,

    pub fn intern(symsafe: *SymbolSafe, x: []const u8) !*Symbol {
        if (symsafe.safe.get(x)) |sym| {
            return sym;
        }
        try symsafe.safe.ensureUnusedCapacity(symsafe.allocator, 1);
        const sp = try Symbol.create(symsafe.allocator, x);
        symsafe.safe.putAssumeCapacity(x, sp);
        return sp;
    }
};

//| Some symbols (due to multiterminals) have the same name as others,
//| specifically their [0] subsym. So we can't keep them in the SymbolSafe:
//| we create a separate freelist to store them.

const SymFreelist = struct {
    sp: *Symbol,
    next: ?*SymFreelist,
};

threadlocal var sym_freelist: ?*SymFreelist = null;

threadlocal var symbol_map: SymbolSafe = undefined;
threadlocal var is_symbol_map = false;

fn Symbol_init(allocator: Allocator) void {
    if (is_symbol_map) return;
    defer is_symbol_map = true;
    symbol_map.allocator = allocator;
    symbol_map.safe = .empty;
}

fn Symbol_free() void {
    dbgassert(is_symbol_map);
    defer is_symbol_map = false;
    for (symbol_map.safe.values()) |v| {
        v.destroy(symbol_map.allocator);
    }
    symbol_map.safe.deinit(symbol_map.allocator);
}

fn Symbol_new(str: []const u8) !*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.intern(str);
}

fn Symbol_count() usize {
    return symbol_map.safe.count();
}

fn Symbol_find(str: []const u8) ?*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.get(str);
}

fn Symbol_arrayof() []*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.values();
}

// /* Compare two symbols for sorting purposes.  Return negative,
// ** zero, or positive if a is less then, equal to, or greater
// ** than b.
// **
// ** Symbols that begin with upper case letters (terminals or tokens)
// ** must sort before symbols that begin with lower case letters
// ** (non-terminals).  And MULTITERMINAL symbols (created using the
// ** %token_class directive) must sort at the very end. Other than
// ** that, the order does not matter.
// **
// ** We find experimentally that leaving the symbols in their original
// ** order (the order they appeared in the grammar file) gives the
// ** smallest parser tables in SQLite.
// */

//| [5840]
//
fn Symbol_lessThanFn(_: void, a: *Symbol, b: *Symbol) bool {
    const a_val: u8 = if (a.type == .multiterminal) 3 else if (a.name[0] > 'Z') 2 else 1;
    const b_val: u8 = if (b.type == .multiterminal) 3 else if (b.name[0] > 'Z') 2 else 1;
    if (a_val < b_val) return true else if (a_val > b_val) return false;
    return (a.index < b.index);
}

//| [1300] configlist.c
//|
//| This is one of the places where the Lemon generator uses global state.
//| No sin in that, not in an application, but we're going to package it up
//| into:

pub const ConfigLists = struct {
    allocator: Allocator,
    pool: MemoryPool(Config),
    current: ?*Config,
    currentend: *?*Config,
    basis: ?*Config,
    basisend: *?*Config,
    config_table: ArrayHashMap(*Config, void, ConfigContext, false),
};

const ConfigContext = struct {
    pub fn eql(_: ConfigContext, c1: *Config, c2: *Config, _: usize) bool {
        return c1.rp.index == c2.rp.index and c1.dot == c2.dot;
    }

    // [5822]
    pub fn hash(_: ConfigContext, c: *Config) u32 {
        // This is where I brag just a little, having spotted an error
        // of no practical significance in lemon.c as it was when I
        // began this:  https://sqlite.org/forum/forumpost/686cb52ae2
        //
        return @intCast(c.rp.index * 37 + c.dot);
    }
};

//| so we only need one global:
threadlocal var cf_ls: ConfigLists = undefined;
threadlocal var is_a_configlists = false;

fn newconfig() !*Config {
    dbgassert(is_a_configlists);
    const cp = try cf_ls.pool.create();
    cp.* = .empty;
    return cp;
}

fn deleteconfig(cfp: *Config) void {
    dbgassert(is_a_configlists);
    cf_ls.pool.destroy(cfp);
}

fn Configlist_init(allocator: Allocator, pool: MemoryPool(Config)) void {
    if (is_a_configlists) return;
    defer is_a_configlists = true;
    cf_ls.allocator = allocator;
    cf_ls.pool = pool;
    cf_ls.current = null;
    cf_ls.currentend = &cf_ls.current;
    cf_ls.basis = null;
    cf_ls.basisend = &cf_ls.basis;
    cf_ls.config_table = .empty;
}

fn Configlist_reset() void {
    dbgassert(is_a_configlists);
    cf_ls.current = null;
    cf_ls.currentend = &cf_ls.current;
    cf_ls.basis = null;
    cf_ls.basisend = &cf_ls.basis;
    cf_ls.config_table.clearRetainingCapacity();
}

/// Add another configuration to the configuration list
fn Configlist_add(rp: *Rule, dot: u32) !*Config {
    dbgassert(is_a_configlists);
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    if (p_check1) {
        dprint("[{d},{d}] ", .{ rp.index, dot });
    }
    const maybe_cfp = cf_ls.config_table.getKey(&model);
    if (p_check1) {
        if (maybe_cfp) |_| {
            dprint("+ ", .{});
        } else {
            dprint(". ", .{});
        }
    }
    if (maybe_cfp) |cfp| {
        return cfp;
    }
    var cfp = try newconfig();
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cf_ls.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    dbgassert(cfp.stp == null);
    dbgassert(cfp.next == null);
    dbgassert(cfp.fplp == null);
    dbgassert(cfp.bplp == null);
    cf_ls.currentend.* = cfp;
    cf_ls.currentend = &cfp.next;
    try cf_ls.config_table.put(cf_ls.allocator, cfp, {});
    return cfp;
}

fn Configlist_addbasis(rp: *Rule, dot: u32) !*Config {
    dbgassert(is_a_configlists);
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    const maybe_cfp = cf_ls.config_table.getKey(&model);
    if (maybe_cfp) |cfp| return cfp;
    var cfp = try newconfig();
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cf_ls.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    dbgassert(cfp.stp == null);
    dbgassert(cfp.next == null);
    dbgassert(cfp.fplp == null);
    dbgassert(cfp.bplp == null);
    cf_ls.currentend.* = cfp;
    cf_ls.currentend = &cfp.next;
    cf_ls.basisend.* = cfp;
    cf_ls.basisend = &cfp.bp;
    try cf_ls.config_table.put(cf_ls.allocator, cfp, {});
    return cfp;
}

// [5642]
//
/// Compare two configurations
fn Configcmp(a: *Config, b: *Config) bool {
    if (a.rp.index < b.rp.index) {
        return true;
    } else if (a.rp.index > b.rp.index) {
        return false;
    } else if (a.dot <= b.dot) {
        return true;
    } else {
        return false;
    }
}

/// Compute the closure of the configuration list
fn Configlist_closure(lemp: *Lemon) !void {
    var this_cfp: ?*Config = cf_ls.current;
    var scan_count: usize = 0;
    scan: while (this_cfp) |cfp| : (this_cfp = cfp.next) {
        scan_count += 1;
        const rp = cfp.rp;
        const dot = cfp.dot;
        if (p_check1) {
            dprint("Closure: {s} #{d}\n", .{ rp.lhs.name, dot });
        }
        if (dot >= rp.rhs.len) continue :scan;
        const sp = rp.rhs[dot];
        if (sp.type == .nonterminal) {
            if (sp.rule == null and sp != lemp.errsym) {
                ErrorMsg(lemp.filename, 0, "" ++
                    "Nonterminal \"{s}\" has no rules.", .{sp.name});
                lemp.errorcnt += 1;
            }
            var this_newrp = sp.rule;
            while (this_newrp) |newrp| : (this_newrp = newrp.nextlhs) {
                if (p_check1) {
                    dprint("    lhs {s}:{d} ", .{ newrp.lhs.name, newrp.index });
                }
                const newcfp = try Configlist_add(newrp, 0);
                var i: usize = dot + 1;
                dots: while (i < rp.nrhs) : (i += 1) {
                    const xsp = rp.rhs[i];
                    if (p_check1) {
                        dprint("{s}, ", .{xsp.name});
                    }
                    // TODO: refactor this: slice in for loop above,
                    // switch statement here:
                    if (xsp.type == .terminal) {
                        _ = SetAdd(newcfp.fws, xsp.index);
                        break :dots;
                    } else if (xsp.type == .multiterminal) {
                        for (xsp.subsym) |subsym| {
                            _ = SetAdd(newcfp.fws, subsym.index);
                        }
                        break :dots;
                    } else {
                        _ = SetUnion(newcfp.fws, xsp.firstset);
                        if (!xsp.lambda) break :dots;
                    }
                }
                if (i == rp.nrhs) try Plink_add(&cfp.fplp, newcfp);
                if (p_check1) {
                    dprint("\n", .{});
                }
            }
        }
    }
    if (p_check1) {
        dprint("    count {d}\n", .{scan_count});
    }
}

const Configlist_msort = mergeSortFn(Config, "next", Configcmp);

fn Configlist_sort() void {
    cf_ls.current = if (cf_ls.current) |cfp| Configlist_msort(cfp) else null;
    cf_ls.currentend = &cf_ls.current;
}

const Configlist_msortBasis = mergeSortFn(Config, "bp", Configcmp);

fn Configlist_sortbasis() void {
    cf_ls.basis = if (cf_ls.basis) |bp| Configlist_msortBasis(bp) else null;
    cf_ls.basisend = &cf_ls.basis;
}
/// Return a pointer to the head of the configuration list
/// and reset the list.
fn Configlist_return() ?*Config {
    const old = cf_ls.current;
    cf_ls.current = null;
    cf_ls.currentend.* = cf_ls.current;
    return old;
}

/// Return a pointer to the head of the configuration basis list
/// and reset the list.
fn Configlist_basis() ?*Config {
    const old = cf_ls.basis;
    cf_ls.basis = null;
    cf_ls.basisend.* = cf_ls.basis;
    return old;
}

/// Free all elements of the given configuration list.
fn Configlist_eat(cfp: ?*Config, allocator: Allocator) void {
    var nextcfp: ?*Config = cfp;
    while (nextcfp) |this_cfp| {
        nextcfp = this_cfp.next;
        dbgassert(this_cfp.fplp == null);
        dbgassert(this_cfp.bplp == null);
        if (this_cfp.fws.len > 0) allocator.free(this_cfp.fws);
        deleteconfig(this_cfp);
    }
}

test "exe mentioned" {
    std.debug.print("hello from lemon main\n", .{});
}
