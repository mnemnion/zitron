//! *************************************************************************
//! Driver template for the Zitron parser generator.
//!
//! The "zitron" program processes an LALR(1) input grammar file, then uses
//! this template to construct a parser.  The "zitron" program inserts text at
//! each "%%" line.  Any occurance of the lemon emoji is used to interpolate
//! values from the generator, in lieu of macros.  Otherwise, the content of
//! this template is copied straight through into the generate parser source
//! file.
//!
//! The following is the concatenation of all %include directives from the
//! input grammar file:
//!


// ************ Begin %include sections from the grammar ************************
%%
// **************** End of %include directives **********************************

const std = @import("std");
const builtin = @import("builtin");

const NDEBUG = builtin.mode == .Debug;

/// This specifies the token enum.  If generated separately this is an import of
///  that file.
/// ***************** Begin token definitions ***********************************
%%
// **************** End token definitions ***************************************
// The next sections is a series of constant definitions dictating
// various aspects of the generated parser.
//
//    YYCODETYPE         is the data type used to store the integer codes
//                       that represent terminal and non-terminal symbols.
//                       "unsigned char" is used if there are fewer than
//                       256 symbols.  Larger types otherwise.
//    YYNOCODE           is a number of type YYCODETYPE that is not used for
//                       any terminal or nonterminal symbol.
//    YYFALLBACK         If defined, this indicates that one or more tokens
//                       (also known as: "terminal symbols") have fall-back
//                       values which should be used if the original symbol
//                       would not parse.  This permits keywords to sometimes
//                       be used as identifiers, for example.
//    YYACTIONTYPE       is the data type used for "action codes" - numbers
//                       that indicate what to do in response to the next
//                       token.
//    YY_TOKEN_TYPE     is the data type used for minor type for terminal
//                       symbols.  Background: A "minor type" is a semantic
//                       value associated with a terminal or non-terminal
//                       symbols.  For example, for an "ID" terminal symbol,
//                       the minor type might be the name of the identifier.
//                       Each non-terminal can have a different minor type.
//                       Terminal symbols all have the same minor type, though.
//                       This macros defines the minor type for terminal
//                       symbols.
//    YYMINORTYPE        is the data type used for all minor types.
//                       This is typically a union of many types, one of
//                       which is YY_TOKEN_TYPE.  The entry in the union
//                       for terminal symbols is called "yy0".
//    YYSTACKDEPTH       is the maximum depth of the parser's stack.  If
//                       zero the stack is dynamically sized using realloc()
//    ParseARG_SDECL     A static variable declaration for the %extra_argument
//    ParseARG_PDECL     A parameter declaration for the %extra_argument
//    ParseARG_PARAM     Code to pass %extra_argument as a subroutine parameter
//    ParseARG_STORE     Code to store %extra_argument into yypParser
//    ParseARG_FETCH     Code to extract %extra_argument from yypParser
//    ParseCTX_*         As ParseARG_ except for %extra_context
//    YYREALLOC          Name of the realloc() function to use
//    YYFREE             Name of the free() function to use
//    YYDYNSTACK         True if stack space should be extended on heap
//    YYERRORSYMBOL      is the code number of the error symbol.  If not
//                       defined, then do no error processing.
//    YYNSTATE           the combined number of states.
//    YYNRULE            the number of rules in the grammar
//    YYNTOKEN           Number of terminal symbols
//    YY_MAX_SHIFT       Maximum value for shift actions
//    YY_MIN_SHIFTREDUCE Minimum value for shift-reduce actions
//    YY_MAX_SHIFTREDUCE Maximum value for shift-reduce actions
//    YY_ERROR_ACTION    The yy_action[] code for syntax error
//    YY_ACCEPT_ACTION   The yy_action[] code for accept
//    YY_NO_ACTION       The yy_action[] code for no-op
//    YY_MIN_REDUCE      Minimum value for reduce actions
//    YY_MAX_REDUCE      Maximum value for reduce actions
//    YY_MIN_DSTRCTR     Minimum symbol value that has a destructor
//    YY_MAX_DSTRCTR     Maximum symbol value that has a destructor
//
// ************* Begin constants *****************************************
%%
// ************* End constants *******************************************

const YY_VOIDTOKEN = @TypeOf(YY_TOKEN_TYPE) == void;

const YY_NLOOKAHEAD = yy_lookahead.len;

/// Set a value for zitron_no_error_recovery to disable error recovery.
const YYNOERRORRECOVERY = !@hasDecl(@This(), "zitron_no_error_recovery");

/// Set a value for zitron_track_max_stack_depth to track the maximum stack depth on the Parser instance.
const YYTRACKMAXSTACKDEPTH = @hasDecl(@This(), "zitron_track_max_stack_depth");

// TODO: Do we keep this growable stack thing around?
const YYGROWABLESTACK = true;

// TODO: stub for coverage (no idea how I plan to handle it, but probably want to)
const YYCOVERAGE = false;

// Next are the tables used to determine what action to take based on the
// current state and lookahead token.  These tables are used to implement
// functions that take a state number and lookahead value and return an
// action integer.
//
// Suppose the action integer is N.  Then the action is determined as
// follows
//
//   0 <= N <= YY_MAX_SHIFT             Shift N.  That is, push the lookahead
//                                      token onto the stack and goto state N.
//
//   N between YY_MIN_SHIFTREDUCE       Shift to an arbitrary state then
//     and YY_MAX_SHIFTREDUCE           reduce by rule N-YY_MIN_SHIFTREDUCE.
//
//   N == YY_ERROR_ACTION               A syntax error has occurred.
//
//   N == YY_ACCEPT_ACTION              The parser accepts its input.
//
//   N == YY_NO_ACTION                  No such action.  Denotes unused
//                                      slots in the yy_action[] table.
//
//   N between YY_MIN_REDUCE            Reduce by rule N-YY_MIN_REDUCE
//     and YY_MAX_REDUCE
//
// The action table is constructed as a single large table named yy_action[].
// Given state S and lookahead X, the action is computed as either:
//
//    (A)   N = yy_action[ yy_shift_ofst[S] + X ]
//    (B)   N = yy_default[S]
//
// The (A) formula is preferred.  The B formula is used instead if
// yy_lookahead[yy_shift_ofst[S]+X] is not equal to X.
//
// The formulas above are for computing the action when the lookahead is
// a terminal symbol.  If the lookahead is a non-terminal (as occurs after
// a reduce action) then the yy_reduce_ofst[] array is used in place of
// the yy_shift_ofst[] array.
//
// The following are the tables generated in this section:
//
//  yy_action[]        A single table containing all actions.
//  yy_lookahead[]     A table containing the lookahead for each entry in
//                     yy_action.  Used to detect hash collisions.
//  yy_shift_ofst[]    For each state, the offset into yy_action for
//                     shifting terminals.
//  yy_reduce_ofst[]   For each state, the offset into yy_action for
//                     shifting non-terminals after a reduce.
//  yy_default[]       Default action for each state.
//
// *********** Begin parsing tables **********************************************/
%%
// /********** End of zitron-generated parsing tables *****************************/
//
// The next table maps tokens (terminal symbols) into fallback tokens.
// If a construct like the following:
//
//      %fallback ID X Y Z.
//
// appears in the grammar, then ID becomes a fallback token for X, Y,
// and Z.  Whenever one of the tokens X, Y, or Z is input to the parser
// but it does not parse, the type of the token is changed to ID and
// the parse is retried before an error is thrown.
//
// This feature can be used, for example, to cause some keywords in a language
// to revert to identifiers if they keyword does not apply in the context where
// it appears.
//
const yyFallback = [_]YYCODETYPE{
%%
};

/// The following structure represents a single element of the
/// parser's stack.  Information stored includes:
///
///   +  The state number for the parser at this level of the stack.
///
///   +  The value of the token stored at this level of the stack.
///      (In other words, the "major" token.)
///
///   +  The semantic value stored at this level of the stack.  This is
///      the information used by the action routines in the grammar.
///      It is sometimes called the "minor" token.
///
/// After the "shift" half of a SHIFTREDUCE action, the stateno field
/// actually contains the reduce action for the second half of the
/// SHIFTREDUCE.
const yyStackEntry = struct {
    /// The state-number, or reduce action in SHIFTREDUCE.
    stateno: YYACTIONTYPE,
    /// The major token value.  This is the code number for the token at this stack level.
    major: YYCODETYPE,
    /// The user-supplied minor token value.  This is the value of the token.
    minor: YYMINORTYPE,
};

/// This value is the minimum amount of memory needed to build the
/// parser stack.
pub const parser_stack_minimum = @sizeOf(🍋PARSER_NAME) + (@sizeOf(yyStackEntry) * YYSTACKDEPTH);

/// The state of the parser is completely contained in an instance of
/// the following structure.
pub const 🍋PARSER_NAME = struct {
    /// Allocator
    allocator: std.mem.Allocator,
    /// Pointer to top element of the stack
    tos: [*]yyStackEntry,
    //
    // TODO: reckon with `yyhwm`
    //
    /// Shifts left before out of the error
    errcnt: isize,
    🍋ARG_SDECL
    🍋CTX_SDECL
    stack_end: [*]yyStackEntry,
    stack: [*]yyStackEntry,
    stk0: []yyStackEntry,

    /// Create a 🍋PARSER_NAME on the heap, returning a pointer to it.
    /// Free later with `destroy`.
    pub fn create(allocator: std.mem.Allocator 🍋CTX_PDECL) !*🍋PARSER_NAME {
        var yypParser = try allocator.create(🍋PARSER_NAME);
        🍋CTX_STORE
        try yypParser.init(allocator, 🍋CTX_PARAM);
        return yypParser;
    }

    /// Free all 🍋PARSER_NAME memory, including the *🍋PARSER_NAME itself.
    pub fn destroy(yypParser: *🍋PARSER_NAME) void {
        yypParser.deinit();
        yypParser.allocator.destroy(yypParser);
    }

    /// Allocate a stack for the 🍋PARSER_NAME and set all fields to their
    /// initial state.  No need to call this if using `create`.  Free later
    /// with `deinit`.
    pub fn init(yypParser: *🍋PARSER_NAME, allocator: std.mem.Allocator 🍋CTX_PDECL) std.mem.Allocator.Error!void {
        🍋CTX_STORE
        yypParser.allocator = allocator;
        yypParser.stk0 = try yypParser.allocator.alloc(yyStackEntry, 100);
        yypParser.stack = yypParser.stk0.ptr;
        yypParser.stack_end = yypParser.stack + (yypParser.stk0.len - 1);
        yypParser.errcnt = -1; // TODO: Deal with NOERRORRECOVERY
        yypParser.tos = yypParser.stack;
        yypParser.stack[0].stateno = 0;
        yypParser.stack[0].major = 0;
        yypParser.stack[0].minor = undefined; // This is ok
    }

    /// Free the stack memory of the parser, first destroying anything
    /// left on the stack.
    pub fn deinit(yypParse: *🍋PARSER_NAME) void {
        yypParse.reset();
        yypParse.allocator.free(yypParse.stk0);
    }

    /// Call this when there are no tokens remaining.
    pub fn finalize(yypParse: *🍋PARSER_NAME 🍋ARG_PDECL) !void {
        // Undefined is ok here, it can't be captured and no
        // destructor will ever be called on it, as determined
        // by the 'major type', .end_of_input.
        try yypParse.parse(.end_of_input, undefined 🍋ARG_PARAM);
    }

    // NOTE: this code is somewhat oddly organized due to being translated from
    // C.  The following will appear as ordinary member functions in the type:

    /// Reset the parser to a known-good state, freeing any
    /// destructable data kept on the parsing stack.  Retains
    /// the parser stack allocation, to free it, call `deinit`,
    /// or just `destroy` if the parser itself is heap-allocated.
    pub const reset = ParseFinalize;

    /// Parse a token.
    pub const parse = yyParse;
};

// TODO: Add ParseTrace


// For tracing shifts, the names of all terminals and nonterminals
// are required.  The following table supplies these names.
pub const yyTokenName = [_][:0]const u8{
%%
};
// For tracing reduce actions, the names of all rules are required.
//
pub const yyRuleName = [_][:0]const u8{
%%
};


/// Try to increase the size of the parser stack.  Throws if the allocation
/// fails.
fn yyGrowStack(yy_p: *🍋PARSER_NAME) !void {
    const yy_new_size = yy_p.stk0.len * 2 + 100;
    const yy_idx = (@intFromPtr(yy_p.tos) - @intFromPtr(yy_p.stack));
    const yyp_new = try yy_p.allocator.realloc(yy_p.stk0, yy_new_size);
    yy_p.stack = yyp_new.ptr;
    yy_p.stk0 = yyp_new;
    yy_p.tos = yyp_new.ptr + yy_idx;
    yy_p.stack_end = yyp_new.ptr + (yy_new_size - 1);
}


/// The following function deletes the "minor type" or semantic value
/// associated with a symbol.  The symbol can be either a terminal
/// or nonterminal. "yymajor" is the symbol code, and "yypminor" is
/// a pointer to the value to be deleted.  The code used to do the
/// deletions is derived from the %destructor and/or %token_destructor
/// directives of the input grammar.
///
fn yy_destructor(
  yypParser: *🍋PARSER_NAME,    // The parser */
  yymajor: YYCODETYPE,     // Type code for object to destroy */
  yypminor: *YYMINORTYPE,   // The object to be destroyed */
) void {
    🍋ARG_FETCH
    🍋CTX_FETCH
    _ = .{ 🍋PARSER_NAME, yypminor }; // Unused variable ward
    const allocator = yypParser.allocator; _ = .{allocator};
    switch( yymajor ){
        // Here is inserted the actions which take place when a
        // terminal or non-terminal is destroyed.  This can happen
        // when the symbol is popped from the stack during a
        // reduce or during error processing or when a parser is
        // being destroyed before it is finished parsing.
        //
        // Note: during a reduce, the only symbols destroyed are those
        // which appear on the RHS of the rule, but which are *not* used
        // inside the C code.
        //
//******** Begin destructor definitions ***************************************/
%%
//******** End destructor definitions *****************************************/
        else =>  {},   // If no destructor action specified: do nothing */
    }
    🍋ARG_STORE
    🍋CTX_STORE
}

const yy_assert = std.debug.assert;

///
/// Pop the parser's stack once.
///
/// If there is a destructor routine associated with the token which
/// is popped from the stack, then call it.
fn yy_pop_parser_stack(pParser: *🍋PARSER_NAME) void {
    yy_assert(@intFromPtr(pParser.tos) > @intFromPtr(pParser.stack));
    pParser.tos -= 1;
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sPopping %s\n",
    //       yyTracePrompt,
    //       yyTokenName[yytos->major]);
    //   }
    // #endif
    yy_destructor(pParser, pParser.tos[0].major, &pParser.tos[0].minor);
}


// TODO: deal with this stuff
//
///
/// Clear all secondary memory allocations from the parser
///
fn ParseFinalize(yypParser: *🍋PARSER_NAME) void {
    var yytos = yypParser.tos;
    while (@intFromPtr(yytos) > @intFromPtr(yypParser.stack)) {
        // #ifndef NDEBUG
        //     if( yyTraceFILE ){
        //       fprintf(yyTraceFILE,"%sPopping %s\n",
        //         yyTracePrompt,
        //         yyTokenName[yytos->major]);
        //     }
        // #endif
        if (yytos[0].major >= YY_MIN_DSTRCTR) {
            yy_destructor(yypParser, yytos[0].major, &yytos[0].minor);
            yytos -= 1;
        }
    }
}

//
// #ifndef Parse_ENGINEALWAYSONSTACK
// /*
// ** Deallocate and destroy a parser.  Destructors are called for
// ** all stack elements before shutting the parser down.
// **
// ** If the YYPARSEFREENEVERNULL macro exists (for example because it
// ** is defined in a %include section of the input grammar) then it is
// ** assumed that the input pointer is never NULL.
// */
// void ParseFree(
//   void *p,                    /* The parser to be deleted */
//   void (*freeProc)(void*)     /* Function used to reclaim memory */
// ){
// #ifndef YYPARSEFREENEVERNULL
//   if( p==0 ) return;
// #endif
//   ParseFinalize(p);
//   (*freeProc)(p);
// }
// #endif /* Parse_ENGINEALWAYSONSTACK */
//
// /*
// ** Return the peak depth of the stack for a parser.
// */
// #ifdef YYTRACKMAXSTACKDEPTH
// int ParseStackPeak(void *p){
//   🍋PARSER_NAME *pParser = (🍋PARSER_NAME*)p;
//   return pParser->yyhwm;
// }
// #endif
//
// /* This array of booleans keeps track of the parser statement
// ** coverage.  The element yycoverage[X][Y] is set when the parser
// ** is in state X and has a lookahead token Y.  In a well-tested
// ** systems, every element of this matrix should end up being set.
// */
// #if defined(YYCOVERAGE)
threadlocal var yycoverage: if (YYCOVERAGE)
                                [YYNSTATE][YYNTOKEN]u8
                            else
                                void = if (YYCOVERAGE)
                                          .{ .{0} ** YYNTOKEN } ** YYNSTATE
                                       else {};
// #endif
//
// /*
// ** Write into out a description of every state/lookahead combination that
// **
// **   (1)  has not been used by the parser, and
// **   (2)  is not a syntax error.
// **
// ** Return the number of missed state/lookahead combinations.
// */
// #if defined(YYCOVERAGE)
// int ParseCoverage(FILE *out){
//   int stateno, iLookAhead, i;
//   int nMissed = 0;
//   for(stateno=0; stateno<YYNSTATE; stateno++){
//     i = yy_shift_ofst[stateno];
//     for(iLookAhead=0; iLookAhead<YYNTOKEN; iLookAhead++){
//       if( yy_lookahead[i+iLookAhead]!=iLookAhead ) continue;
//       if( yycoverage[stateno][iLookAhead]==0 ) nMissed++;
//       if( out ){
//         fprintf(out,"State %d lookahead %s %s\n", stateno,
//                 yyTokenName[iLookAhead],
//                 yycoverage[stateno][iLookAhead] ? "ok" : "missed");
//       }
//     }
//   }
//   return nMissed;
// }
// #endif
//

/// Find the appropriate action for a parser given the terminal
/// look-ahead token iLookAhead.
fn yy_find_shift_action(
    /// The look-ahead token
    iLookAhead: YYCODETYPE,
    /// Current state number
    stateno: YYACTIONTYPE,
) YYACTIONTYPE {
    if (stateno > YY_MAX_SHIFT) return stateno;
    yy_assert(stateno <= YY_SHIFT_COUNT);
    if (comptime YYCOVERAGE) {
        yycoverage[stateno][iLookAhead] = 1;
    }
    var iLook = iLookAhead;
    while (true) {
        var i = yy_shift_ofst[stateno];
        yy_assert(i >= 0);
        yy_assert(i <= YY_ACTTAB_COUNT);
        yy_assert(i+YYNTOKEN <= YY_NLOOKAHEAD);
        yy_assert(iLook != YYNOCODE);
        yy_assert(iLook < YYNTOKEN);
        i += iLook;
        yy_assert(i < YY_NLOOKAHEAD);
        if(yy_lookahead[i] != iLook) {
            if (comptime YYFALLBACK) {
                yy_assert(iLook < yyFallback.len);
                const iFallback: YYCODETYPE = yyFallback[iLook];
                if (iFallback != 0) {
                    // #ifndef NDEBUG
                    //         if( yyTraceFILE ){
                    //           fprintf(yyTraceFILE, "%sFALLBACK %s => %s\n",
                    //              yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[iFallback]);
                    //         }
                    // #endif
                    yy_assert(yyFallback[iFallback] == 0) ; // Fallback loop must terminate */
                    iLook = iFallback;
                    continue;
                }
            }
            if (comptime YY_HASWILDCARD) {
                const j: YYCODETYPE = i - iLook + YYWILDCARD;
                yy_assert(j < yy_lookahead.len);
                if (yy_lookahead[j] == YYWILDCARD and iLook > 0) {
                    // #ifndef NDEBUG
                    //           if( yyTraceFILE ){
                    //             fprintf(yyTraceFILE, "%sWILDCARD %s => %s\n",
                    //                yyTracePrompt, yyTokenName[iLookAhead],
                    //                yyTokenName[YYWILDCARD]);
                    //           }
                    // #endif /* NDEBUG */
                    return yy_action[j];
                }
            }
            return yy_default[stateno];
        }else{
            yy_assert(i < yy_action.len);
            return yy_action[i];
        }
    }
}


/// Find the appropriate action for a parser given the non-terminal
/// look-ahead token iLookAhead.
fn yy_find_reduce_action(
    /// Current state number
    stateno: YYACTIONTYPE ,
    /// The look-ahead token
    iLookAhead: YYCODETYPE ,
) YYACTIONTYPE {
    if (comptime YYHAS_ERRORSYMBOL) {
        if (stateno > YY_REDUCE_COUNT) {
          return yy_default[stateno];
        }
    } else {
      yy_assert(stateno <= YY_REDUCE_COUNT);
    }
    var i: isize = yy_reduce_ofst[stateno];
    yy_assert(iLookAhead != YYNOCODE);
    i += iLookAhead;
    if (comptime YYHAS_ERRORSYMBOL) {
        if (i < 0 or i >= YY_ACTTAB_COUNT or yy_lookahead[@intCast(i)] != iLookAhead) {
            return yy_default[stateno];
        }
    } else {
        yy_assert( i >= 0 and i < YY_ACTTAB_COUNT );
        yy_assert( yy_lookahead[@intCast(i)]==iLookAhead );
    }
    return yy_action[@intCast(i)];
}

/// The following routine is called if the stack overflows.
fn yyStackOverflow(yypParser: *🍋PARSER_NAME) !void {
    // Justify the !
    if (false) return error.YyImpossibleError;
    🍋ARG_FETCH
    🍋CTX_FETCH
    // #ifndef NDEBUG
    //    if( yyTraceFILE ){
    //      fprintf(yyTraceFILE,"%sStack Overflow!\n",yyTracePrompt);
    //    }
    // #endif
    while (@intFromPtr(yypParser.tos) > @intFromPtr(yypParser.stack)) yy_pop_parser_stack(yypParser);
    // Here code is inserted which will execute if the parser
    // stack ever overflows.
    { // This lets us re-throw:
//******* Begin %stack_overflow code ******************************************/
%%
//******* End %stack_overflow code ********************************************/
    } // The cost: rare, non-pointer uses of ctx and arg will not get stored
    🍋ARG_STORE // Suppress warning about unused %extra_argument var
    🍋CTX_STORE
}

///
/// Print tracing information for a SHIFT action
fn yyTraceShift(yypParser: *🍋PARSER_NAME, yyNewState: usize, zTag: []const u8) void {
    if (comptime !NDEBUG) {
        _ = .{yypParser, yyNewState, zTag};
    }
}
// #ifndef NDEBUG
// static void yyTraceShift(🍋PARSER_NAME *yypParser, int yyNewState, const char *zTag){
//   if( yyTraceFILE ){
//     if( yyNewState<YYNSTATE ){
//       fprintf(yyTraceFILE,"%s%s '%s', go to state %d\n",
//          yyTracePrompt, zTag, yyTokenName[yypParser->yytos->major],
//          yyNewState);
//     }else{
//       fprintf(yyTraceFILE,"%s%s '%s', pending reduce %d\n",
//          yyTracePrompt, zTag, yyTokenName[yypParser->yytos->major],
//          yyNewState - YY_MIN_REDUCE);
//     }
//   }
// }
// #else
// # define yyTraceShift(X,Y,Z)
// #endif

/// Perform a shift action.
fn yy_shift(
    /// The parser to be shifted
    yypParser: *🍋PARSER_NAME,
    /// The new state to shift in
    yyNewState: YYACTIONTYPE,
    /// The major token to shift in
    yyMajor: YYCODETYPE,
    /// The minor token to shift in
    yyMinor: YY_TOKEN_TYPE,
) void {
    yypParser.tos += 1;
    // #ifdef YYTRACKMAXSTACKDEPTH
    //     if( (int)(yypParser->yytos - yypParser->yystack)>yypParser->yyhwm ){
    //     yypParser->yyhwm++;
    //     yy_assert( yypParser->yyhwm == (int)(yypParser->yytos - yypParser->yystack) );
    //     }
    // #endif
    var yytos = yypParser.tos;
    var yy_new = yyNewState;
    if (@intFromPtr(yytos) > @intFromPtr(yypParser.stack_end)) {
        yyGrowStack(yypParser) catch  {
            yypParser.tos -= 1;
            try yyStackOverflow(yypParser);
            return;
        };
        yytos = yypParser.tos;
        yy_assert(@intFromPtr(yytos) <= @intFromPtr(yypParser.stack_end));
    }
    if (yy_new > YY_MAX_SHIFT) {
        yy_new += YY_MIN_REDUCE - YY_MIN_SHIFTREDUCE;
    }
    yytos[0].stateno = yy_new;
    yytos[0].major = yyMajor;
    yytos[0].minor.yy0 = yyMinor;
    yyTraceShift(yypParser, yy_new, "Shift");
}

/// For rule J, yyRuleInfoLhs[J] contains the symbol on the left-hand side
/// of that rule */
const yyRuleInfoLhs: []const YYCODETYPE = &.{
%%
};

// TODO: is a 128 symbol RHS arbitrary? I mean it is but, in a bad way?
// more seems nuts

/// For rule J, yyRuleInfoNRhs[J] contains the negative of the number
/// of symbols on the right-hand side of that rule.
const yyRuleInfoNRhs: []const i8 = &.{
%%
};

/// Perform a reduce action and the shift that must immediately
/// follow the reduce.
///
/// The yyLookahead and yyLookaheadToken parameters provide reduce actions
/// access to the lookahead token (if any).  The yyLookahead will be YYNOCODE
/// if the lookahead token has already been consumed.  As this procedure is
/// only called from one place, optimizing compilers will in-line it, which
/// means that the extra parameters have no performance impact.
fn yy_reduce(
    /// The parser
    yypParser: *🍋PARSER_NAME,
    /// Number of the rule by which to reduce
    yyruleno: usize,
    /// Lookahead token, or YYNOCODE if none
    yyLookahead: YYCODETYPE,
    /// Value of the lookahead token */
    yyLookaheadToken: YY_TOKEN_TYPE
) !YYACTIONTYPE {
    if (false) return error.YyImpossibleFakeError; // Now user code is throwable
    🍋ARG_FETCH
    🍋CTX_FETCH
    _ = .{yyruleno, yyLookahead, yyLookaheadToken};
    var yymsp = yypParser.tos;
    const allocator = yypParser.allocator; _ = .{allocator};
    var yylhsminor: YYMINORTYPE = undefined; _ = .{&yylhsminor};
    const yysize = yyRuleInfoNRhs[yyruleno];
    errdefer {
        // If user code throws, we trim the stack, including
        // where the reduced action was supposed to go.
        yymsp = yymsp  - @abs(yysize);
        yypParser.tos = yymsp;
    }
    switch( yyruleno ){
    // Beginning here are the reduction cases.  A typical example
    // follows:
    //   0,
    //  #line <lineno> <grammarfile>
    //     => { ... },           // User supplied code
    //  #line <lineno> <thisfile>
    //
//********* Begin reduce actions **********************************************/
%%
//********* End reduce actions ************************************************/
    }
    yy_assert(yyruleno < yyRuleInfoLhs.len);
    const yygoto = yyRuleInfoLhs[yyruleno];
    const yyact = yy_find_reduce_action((yymsp - @abs(yysize))[0].stateno, yygoto);

    // There are no SHIFTREDUCE actions on nonterminals because the table
    // generator has simplified them to pure REDUCE actions.
    yy_assert(!(yyact > YY_MAX_SHIFT and yyact <= YY_MAX_SHIFTREDUCE));

    // It is not possible for a REDUCE to be followed by an error
    yy_assert(yyact != YY_ERROR_ACTION);

    yymsp = yymsp + 1 - @abs(yysize);
    yypParser.tos = yymsp;
    yymsp[0].stateno = yyact;
    yymsp[0].major = yygoto;
    yyTraceShift(yypParser, yyact, "... then shift");
    🍋ARG_STORE
    🍋CTX_STORE
    return yyact;
}

/// The following code executes when the parse fails
fn yy_parse_failed(
    /// The parser
    yypParser: *🍋PARSER_NAME,
) !void {
    if (false) return error.YyImpossibleFakeError; // Now user code is throwable
    🍋ARG_FETCH
    🍋CTX_FETCH
    const allocator = yypParser.allocator; _ = .{allocator};
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sFail!\n",yyTracePrompt);
    //   }
    // #endif
    while (@intFromPtr(yypParser.tos) > @intFromPtr(yypParser.stack))
        yy_pop_parser_stack(yypParser);
    // Here code is inserted which will be executed whenever the
    // parser fails.
    { // Throw guard
//*********** Begin %parse_failure code ***************************************/
%%
//*********** End %parse_failure code *****************************************/
    }
    🍋ARG_STORE // Suppress warning about unused %extra_argument variable
    🍋CTX_STORE
}

/// The following code executes when a syntax error first occurs.
fn yy_syntax_error(
    /// The parser */
    yypParser: *🍋PARSER_NAME,
    /// The major type of the error token */
    yymajor: YYCODETYPE,
    /// The minor type of the error token */
    yyminor: YY_TOKEN_TYPE,
) !void {
    if (false) return error.YyImpossibleFakeError; // Now user code is throwable
    🍋ARG_FETCH
    🍋CTX_FETCH
    const err_token = yyminor;
    const allocator = yypParser.allocator;
    _ = .{ err_token, yymajor, allocator };
    {
//*********** Begin %syntax_error code ****************************************/
%%
//*********** End %syntax_error code ******************************************/
    }
    🍋ARG_STORE
    🍋CTX_STORE
}

/// The following is executed when the parser accepts
fn yy_accept(
    /// The parser
    yypParser: *🍋PARSER_NAME,
) !void {
    if (false) return error.YyImpossibleFakeError; // Now user code is throwable
    🍋ARG_FETCH
    🍋CTX_FETCH
    const allocator = yypParser.allocator; _ = .{allocator};
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sAccept!\n",yyTracePrompt);
    //   }
    // #endif
    if (comptime YYNOERRORRECOVERY) {
        yypParser.errcnt = -1;
    }
    yy_assert(yypParser.tos == yypParser.stack);
    // Here code is inserted which will be executed whenever the
    // parser accepts.
    {
//********** Begin %parse_accept code *****************************************/
%%
//********** End %parse_accept code *******************************************/
    }
    🍋ARG_STORE // Suppress warning about unused %extra_argument variable */
    🍋CTX_STORE
}

/// Cast the token number to its affiliated enum
inline fn yyEnum(yymajor: YYCODETYPE) 🍋TOKEN_ENUM {
    return @enumFromInt(yymajor);
}

// TODO: This could return the context when there is one, and
// `void` otherwise.  That wouldn't be excessively tricksy to
// code up.
//
/// The main parser program.
/// The first argument is a pointer to a structure obtained from
/// "ParseAlloc" which describes the current state of the parser.
/// The second argument is the major token number.  The third is
/// the minor token.  The fourth optional argument is whatever the
/// user wants (and specified in the grammar) and is available for
/// use by the action routines.
///
/// - Inputs:
///
///   - A pointer to the parser (an opaque structure.)
///   - The major token number.
///   - The minor token number.
///   - An option argument of a grammar-specified type.
///
/// - Outputs:
///
///   - None.
///
fn yyParse(
    /// The parser
    yypParser: *🍋PARSER_NAME,
    /// The major token enum
    yy_token: 🍋TOKEN_ENUM,
    /// The value for the token
    yyminor: YY_TOKEN_TYPE
    🍋ARG_PDECL               // Optional %extra_argument parameter
) !void {
    var yyminorunion: YYMINORTYPE = undefined;
    var yyact: YYACTIONTYPE = undefined;   // The parser action.
    var yyendofinput: bool = false;
    var yyerrorhit: bool = false;
    const yymajor: YYCODETYPE = @intFromEnum(yy_token);
    🍋ARG_STORE
    if (comptime (!YYHAS_ERRORSYMBOL and !YYNOERRORRECOVERY)) {
        yyendofinput = (yymajor==0);
    }
    yyact = yypParser.tos[0].stateno;
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     if( yyact < YY_MIN_REDUCE ){
    //       fprintf(yyTraceFILE,"%sInput '%s' in state %d\n",
    //               yyTracePrompt,yyTokenName[yymajor],yyact);
    //     }else{
    //       fprintf(yyTraceFILE,"%sInput '%s' with pending reduce %d\n",
    //               yyTracePrompt,yyTokenName[yymajor],yyact-YY_MIN_REDUCE);
    //     }
    //   }
    // #endif

    while (true) { // Exit by "break"
        yy_assert(@intFromPtr(yypParser.tos) >= @intFromPtr(yypParser.stack));
        yy_assert(yyact == yypParser.tos[0].stateno);
        yyact = yy_find_shift_action(yymajor, yyact);
        if( yyact >= YY_MIN_REDUCE ){
            const yyruleno = yyact - YY_MIN_REDUCE; // Reduce by this rule
            // #ifndef NDEBUG
            //       yy_assert( yyruleno<(int)(sizeof(yyRuleName)/sizeof(yyRuleName[0])) );
            //       if( yyTraceFILE ){
            //         int yysize = yyRuleInfoNRhs[yyruleno];
            //         if( yysize ){
            //           fprintf(yyTraceFILE, "%sReduce %d [%s]%s, pop back to state %d.\n",
            //             yyTracePrompt,
            //             yyruleno, yyRuleName[yyruleno],
            //             yyruleno<YYNRULE_WITH_ACTION ? "" : " without external action",
            //             yypParser->yytos[yysize].stateno);
            //         }else{
            //           fprintf(yyTraceFILE, "%sReduce %d [%s]%s.\n",
            //             yyTracePrompt, yyruleno, yyRuleName[yyruleno],
            //             yyruleno<YYNRULE_WITH_ACTION ? "" : " without external action");
            //         }
            //       }
            // #endif /* NDEBUG */

            // Check that the stack is large enough to grow by a single entry
            // if the RHS of the rule is empty.  This ensures that there is room
            // enough on the stack to push the LHS value.
            if (yyRuleInfoNRhs[yyruleno] == 0) {
                // if ((comptime YYTRACKMAXSTACKDEPTH))
                // and (yypParser.tos - yypParser.stack) > yypParser.yyhwm)
                // {
                //     yypParser.yyhwm += 1;
                //     yy_assert(yypParser.yyhwm == yypParser.yytos - yypParser.yystack);
                // }
                if (@intFromPtr(yypParser.tos) >= @intFromPtr(yypParser.stack_end)) {
                    yyGrowStack(yypParser) catch {
                        try yyStackOverflow(yypParser);
                        break;
                    };
                }
            }
            yyact = try yy_reduce(yypParser, yyruleno, yymajor, yyminor);
        } else if (yyact <= YY_MAX_SHIFTREDUCE) {
            yy_shift(yypParser, yyact, yymajor, yyminor);
            if (comptime !YYNOERRORRECOVERY) {
                yypParser.yyerrcnt -= 1;
            }
            break;
        } else if (yyact == YY_ACCEPT_ACTION) {
            yypParser.tos -= 1;
            try yy_accept(yypParser);
            return;
        } else {
            yy_assert( yyact == YY_ERROR_ACTION );
            yyminorunion = .{.yy0 = yyminor};
            // #ifndef NDEBUG
            //       if( yyTraceFILE ){
            //         fprintf(yyTraceFILE,"%sSyntax Error!\n",yyTracePrompt);
            //       }
            // #endif

            // A syntax error has occurred.
            // The response to an error depends upon whether or not the
            // grammar defines an error token "ERROR".
            //
            if (comptime YYHAS_ERRORSYMBOL) {
                // This is what we do if the grammar does define ERROR:
                //
                //  * Call the %syntax_error function.
                //
                //  * Begin popping the stack until we enter a state where
                //    it is legal to shift the error symbol, then shift
                //    the error symbol.
                //
                //  * Set the error count to three.
                //
                //  * Begin accepting and shifting new tokens.  No new error
                //    processing will occur until three tokens have been
                //    shifted successfully.
                //
                //
                if (yypParser.errcnt < 0) {
                    try yy_syntax_error(yypParser, yymajor, yyminor);
                }
                const yymx = yypParser.tos[0].major;
                if (yymx == @This().YYERRORSYMBOL or yyerrorhit) {
                    // #ifndef NDEBUG
                    //         if( yyTraceFILE ){
                    //           fprintf(yyTraceFILE,"%sDiscard input token %s\n",
                    //              yyTracePrompt,yyTokenName[yymajor]);
                    //         }
                    // #endif
                    yy_destructor(yypParser, yymajor, &yyminorunion);
                    yymajor = YYNOCODE;
                } else {
                    while (yypParser.tos > yypParser.stack) {
                        yyact = yy_find_reduce_action(yypParser.tos[0].stateno, @This().YYERRORSYMBOL);
                        if (yyact <= YY_MAX_SHIFTREDUCE) break;
                        yy_pop_parser_stack(yypParser);
                    }
                    if (yypParser.tos <= yypParser.stack or yymajor == 0) {
                        yy_destructor(yypParser, yymajor, &yyminorunion);
                        try yy_parse_failed(yypParser);
                        if (comptime !YYNOERRORRECOVERY) {
                            yypParser.yyerrcnt = null;
                        }
                        yymajor = YYNOCODE;
                    } else if (yymx != @This().YYERRORSYMBOL) {
                        yy_shift(yypParser, yyact, @This().YYERRORSYMBOL, yyminor);
                    }
                }
                yypParser.errcnt = 3;
                yyerrorhit = true;
                if (yymajor == YYNOCODE) break;
                yyact = yypParser.tos[0].stateno;
            } else if (comptime YYNOERRORRECOVERY) {
                // If the YYNOERRORRECOVERY macro is defined, then do not attempt to
                // do any kind of error recovery.  Instead, simply invoke the syntax
                // error routine and continue going as if nothing had happened.
                //
                // Applications can set this macro (for example inside %include) if
                // they intend to abandon the parse upon the first syntax error seen.
                //
                try yy_syntax_error(yypParser, yymajor, yyminor);
                yy_destructor(yypParser, yymajor, &yyminorunion);
                break;
            } else { // YYERRORSYMBOL is not defined, nor YYNOERRORRECOVERY
                // This is what we do if the grammar does not define ERROR:
                //
                //  * Report an error message, and throw away the input token.
                //
                //  * If the input token is $, then fail the parse.
                //
                // As before, subsequent error messages are suppressed until
                // three input tokens have been successfully shifted.
                //
                if (yypParser.errcnt <= 0) {
                    try yy_syntax_error(yypParser, yymajor, yyminor);
                }
                yypParser.errcnt = 3;
                yy_destructor(yypParser, yymajor, &yyminorunion);
                if( yyendofinput ){
                    try yy_parse_failed(yypParser);
                    if (comptime !YYNOERRORRECOVERY) {
                          yypParser.errcnt = -1;
                    }
                }
                break;
            }
        }
    }
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     yyStackEntry *i;
    //     char cDiv = '[';
    //     fprintf(yyTraceFILE,"%sReturn. Stack=",yyTracePrompt);
    //     for(i=&yypParser->yystack[1]; i<=yypParser->yytos; i++){
    //       fprintf(yyTraceFILE,"%c%s", cDiv, yyTokenName[i->major]);
    //       cDiv = ' ';
    //     }
    //     fprintf(yyTraceFILE,"]\n");
    //   }
    // #endif
    return;
}

