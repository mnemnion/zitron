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
//  This specifies the token enum.  If generated separately this is an import of
//  that file.
// ***************** Begin token definitions *************************************
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
//    ParseTOKENTYPE     is the data type used for minor type for terminal
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
//                       which is ParseTOKENTYPE.  The entry in the union
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
// /********** End of lemon-generated parsing tables *****************************/
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
//
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
//
/// The state of the parser is completely contained in an instance of
/// the following structure.
pub const yyParser = struct {
    /// Allocator
    allocator: Allocator,
    /// Pointer to top element of the stack
    tos: [*]yyStackEntry,
    //
    // TODO: reckon with `yyhym`
    //
    /// Shifts left before out of the error
    errcnt: ?usize,
    🍋ARG_SDECL
    🍋CTX_SDECL
    stack_end: [*]yyStackEntry,
    stack: [*]yyStackEntry,
    stk0: []yyStackEntry,

    pub fn create(allocator: Allocator 🍋CTX_PDECL) !*yyParser {
        var p = try allocator.create(yyParser);
        🍋CTX_STORE
        p.init(🍋CTX_PARAM);
        return p;
    }

    pub fn init(p: *yyParser 🍋CTX_PDECL) void {
        🍋CTX_STORE
        p.stack = p.stk0.ptr;
        p.stack_end = &p.stack[p.stack.len - 1];
        p.errcnt = null; // TODO: Deal with NOERRORRECOVERY
        p.tos = p.stack;
        p.stack[0].stateno = 0;
        p.stack[0].major = 0;
    }

    pub fn growStack = yyGrowStack;
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


/// Try to increase the size of the parser stack.  Return the number
/// of errors.  Return 0 on success.
fn yyGrowStack(p: *yyParser) !void {
    // TODO: yyGrowableStack config, always return error
    const new_size = p.stk0.len * 2 + 100;
    const idx = (@intFromPtr(p.tos) - @intFromPtr(p.stack));
    const p_new = try p.allocator.realloc(p.stk0, new_size);
    p.stack = p_new.ptr;
    p.stk0 = p_new;
    p.tos = &p_new[idx];
    p.stack_end = &p_new[new_size - 1];
}


/// The following function deletes the "minor type" or semantic value
/// associated with a symbol.  The symbol can be either a terminal
/// or nonterminal. "yymajor" is the symbol code, and "yypminor" is
/// a pointer to the value to be deleted.  The code used to do the
/// deletions is derived from the %destructor and/or %token_destructor
/// directives of the input grammar.
///
fn yy_destructor(
  yypParser: *yyParser,    // The parser */
  yymajor: YYCODETYPE,     // Type code for object to destroy */
  yypminor: *YYMINORTYPE,   // The object to be destroyed */
) !void {
    🍋ARG_FETCH
    🍋CTX_FETCH
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
        else =>  break,   // If no destructor action specified: do nothing */
    }
}

const assert = std.debug.assert;

///
/// Pop the parser's stack once.
///
/// If there is a destructor routine associated with the token which
/// is popped from the stack, then call it.
fn yy_pop_parser_stack(pParser: * yyParser) void {
    assert(pParser.tos > pParser.stack);
    pParser.tos -= 1;
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sPopping %s\n",
    //       yyTracePrompt,
    //       yyTokenName[yytos->major]);
    //   }
    // #endif
    yy_destructor(pParser, pParser.tos.major, &pParser.tos.minor);
}


// TODO: deal with this stuff
//
// /*
// ** Clear all secondary memory allocations from the parser
// */
// void ParseFinalize(void *p){
//   yyParser *pParser = (yyParser*)p;
//
//   /* In-lined version of calling yy_pop_parser_stack() for each
//   ** element left in the stack */
//   yyStackEntry *yytos = pParser->yytos;
//   while( yytos>pParser->yystack ){
// #ifndef NDEBUG
//     if( yyTraceFILE ){
//       fprintf(yyTraceFILE,"%sPopping %s\n",
//         yyTracePrompt,
//         yyTokenName[yytos->major]);
//     }
// #endif
//     if( yytos->major>=YY_MIN_DSTRCTR ){
//       yy_destructor(pParser, yytos->major, &yytos->minor);
//     }
//     yytos--;
//   }
//
// #if YYGROWABLESTACK
//   if( pParser->yystack!=pParser->yystk0 ) YYFREE(pParser->yystack);
// #endif
// }
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
//   yyParser *pParser = (yyParser*)p;
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
// static unsigned char yycoverage[YYNSTATE][YYNTOKEN];
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
    assert(stateno <= YY_SHIFT_COUNT);
    if (comptime YYCOVERAGE) {
        yycoverage[stateno][iLookAhead] = 1;
    }
    var iLook = iLookAhead;
    while (true) {
        var i = yy_shift_ofst[stateno];
        assert(i >= 0);
        assert(i <= YY_ACTTAB_COUNT);
        assert(i+YYNTOKEN <= YY_NLOOKAHEAD);
        assert(iLook != YYNOCODE);
        assert(iLook < YYNTOKEN);
        i += iLook;
        assert(i < YY_NLOOKAHEAD);
        if(yy_lookahead[i] != iLook) {
            if (comptime YYFALLBACK) {
                assert(iLook M yyFallback.len);
                const iFallback: YYCODETYPE = yyFallback[iLook];
                if (iFallback != 0) {
                    // #ifndef NDEBUG
                    //         if( yyTraceFILE ){
                    //           fprintf(yyTraceFILE, "%sFALLBACK %s => %s\n",
                    //              yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[iFallback]);
                    //         }
                    // #endif
                    assert(yyFallback[iFallback] == 0) ; // Fallback loop must terminate */
                    iLook = iFallback;
                    continue;
                }
            }
            if (comptime YY_HASWILDCARD) {
                const j: YYCODETYPE = i - iLook + YYWILDCARD;
                assert(j < yy_lookahead.len);
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
            assert(i < yy_action.len);
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
    if (comptime YYERRORSYMBOL) {
        if (stateno > YY_REDUCE_COUNT) {
          return yy_default[stateno];
        }
    } else {
      assert(stateno <= YY_REDUCE_COUNT);
    }
    var i = yy_reduce_ofst[stateno];
    assert(iLookAhead != YYNOCODE);
    i += iLookAhead;
    if (comptime YYERRORSYMBOL)
        if (i < 0 || i >= YY_ACTTAB_COUNT || yy_lookahead[i] != iLookAhead) {
            return yy_default[stateno];
        }
    } else {
        assert( i>=0 && i<YY_ACTTAB_COUNT );
        assert( yy_lookahead[i]==iLookAhead );
    }
    return yy_action[i];
}

/// The following routine is called if the stack overflows.
fn yyStackOverflow(yypParser: *yyParser) void {
   🍋ARG_FETCH
   🍋CTX_FETCH
    // #ifndef NDEBUG
    //    if( yyTraceFILE ){
    //      fprintf(yyTraceFILE,"%sStack Overflow!\n",yyTracePrompt);
    //    }
    // #endif
   while (yypParser.tos > yypParser.stack) yy_pop_parser_stack(yypParser);
   // Here code is inserted which will execute if the parser
   // stack every overflows
//******* Begin %stack_overflow code ******************************************/
%%
//******* End %stack_overflow code ********************************************/
   🍋ARG_STORE // Suppress warning about unused %extra_argument var
   🍋CTX_STORE
}

// /*
// ** Print tracing information for a SHIFT action
// */
// #ifndef NDEBUG
// static void yyTraceShift(yyParser *yypParser, int yyNewState, const char *zTag){
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
    yypParser: *yyParser,
    /// The new state to shift in
    yyNewState: YYACTIONTYPE,
    /// The major token to shift in
    yyMajor: YYCODETYPE,
    /// The minor token to shift in
    yyMinor: ParseTOKENTYPE,
) void {
    yypParser.tos += 1;
    // #ifdef YYTRACKMAXSTACKDEPTH
    //     if( (int)(yypParser->yytos - yypParser->yystack)>yypParser->yyhwm ){
    //     yypParser->yyhwm++;
    //     assert( yypParser->yyhwm == (int)(yypParser->yytos - yypParser->yystack) );
    //     }
    // #endif
    var yytos = yypParser.tos;
    var yy_new = yyNewState;
    if (yytos > yypParser.stack_end) {
        if (yyGrowStack(yypParser)) {
          yypParser.tos -= 1;
          yyStackOverflow(yypParser);
          return;
        }
        yytos = yypParser.tos;
        assert(yytos <= yypParser.stack_end);
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
const yyRuleInfoLhs: []YYCODETYPE = &.{
%%
};

/// For rule J, yyRuleInfoNRhs[J] contains the negative of the number
/// of symbols on the right-hand side of that rule. */
const yyRuleInfoNRhs: []i8 = &.{
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
    yypParser: *yyParser,
    /// Number of the rule by which to reduce
    yyruleno: usize,
    /// Lookahead token, or YYNOCODE if none
    yyLookahead: YYCODETYPE,
    /// Value of the lookahead token */
    yyLookaheadToken: ParseTOKENTYPE,
    🍋CTX_PDECL                   // %extra_context */
) YYACTIONTYPE {
    🍋ARG_FETCH
    _ = .{yyruleno, yyLookahead, yyLookaheadToken};
    var yymsp = yypParser->yytos;
    const allocator = yypParser.allocator; _ = .{allocator};

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
    assert(yyruleno < yyRuleInfoLhs.len);
    const yygoto = yyRuleInfoLhs[yyruleno];
    const yysize = yyRuleInfoNRhs[yyruleno];
    const yyact = yy_find_reduce_action(yymsp[yysize].stateno, yygoto);

    // There are no SHIFTREDUCE actions on nonterminals because the table
    // generator has simplified them to pure REDUCE actions.
    assert(!(yyact > YY_MAX_SHIFT and yyact <= YY_MAX_SHIFTREDUCE));

    // It is not possible for a REDUCE to be followed by an error
    assert(yyact != YY_ERROR_ACTION);

    yymsp += yysize+1;
    yypParser.yytos = yymsp;
    yymsp.stateno = yyct;
    yymsp.major = yygoto;
    yyTraceShift(yypParser, yyact, "... then shift");
    return yyact;
}

// TODO: this should be able to throw yeah?
/// The following code executes when the parse fails
fn yy_parse_failed(
    /// The parser
    yypParser: *yyParser,
) void {
    🍋ARG_FETCH
    🍋CTX_FETCH
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sFail!\n",yyTracePrompt);
    //   }
    // #endif
    while (yypParser.tos > yypParser.stack)
        yy_pop_parser_stack(yypParser);
    // Here code is inserted which will be executed whenever the
    // parser fails.
//*********** Begin %parse_failure code ***************************************/
%%
//*********** End %parse_failure code *****************************************/
    🍋ARG_STORE // Suppress warning about unused %extra_argument variable
    🍋CTX_STORE
}

/// The following code executes when a syntax error first occurs.
fn yy_syntax_error(
    /// The parser */
    yypParser: *yyParser,
    /// The major type of the error token */
    yymajor: int,
    /// The minor type of the error token */
    yyminor: ParseTOKENTYPE,
) void {
    🍋ARG_FETCH
    🍋CTX_FETCH
    const TOKEN = yyminor;
//*********** Begin %syntax_error code ****************************************/
%%
//*********** End %syntax_error code ******************************************/
  🍋ARG_STORE // Suppress warning about unused %extra_argument variable */
  🍋CTX_STORE
}

/// The following is executed when the parser accepts
fn yy_accept(
    /// The parser
    yyParser: *yypParser,
) void {
    🍋ARG_FETCH
    🍋CTX_FETCH
    // #ifndef NDEBUG
    //   if( yyTraceFILE ){
    //     fprintf(yyTraceFILE,"%sAccept!\n",yyTracePrompt);
    //   }
    // #endif
    if (comptime YYNOERRORRECOVERY) {
        yypParser->errcnt = null;
    }
    assert(yypParser.tos == yypParser.stack);
  // Here code is inserted which will be executed whenever the
  // parser accepts.
//********** Begin %parse_accept code *****************************************/
%%
//********** End %parse_accept code *******************************************/
    🍋ARG_STORE // Suppress warning about unused %extra_argument variable */
    🍋CTX_STORE
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
pub fn Parse(
    /// The parser
    yypParser: *yyParser,
    /// The major token code number
    yymajor: int,
    /// The value for the token
    yyminor: ParseTOKENTYPE,
    🍋ARG_PDECL               // Optional %extra_argument parameter
) !void {
    var yyminorunion: YYMINORTYPE = undefined;
    var yyact: YYACTIONTYPE = undefined;   // The parser action.
    var yyendofinput: bool = false;
    var yyerrorhit: bool = false;
    ParseCTX_FETCH
    ParseARG_STORE
    assert(yypParser.yytos != 0);
    if (comptime (!YYERROSYMBOL and !YYNOERRORRECOVERY)) {
        yyendofinput = (yymajor==0);
    }
    var yyact = yypParser.yytos[0].stateno;
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
        assert(yypParser.yytos >= yypParser.yystack);
        assert(yyact == yypParser.yytos[0].stateno);
        yyact = yy_find_shift_action(yymajor, yyact);
        if( yyact >= YY_MIN_REDUCE ){
            const yyruleno = yyact - YY_MIN_REDUCE; // Reduce by this rule
            // #ifndef NDEBUG
            //       assert( yyruleno<(int)(sizeof(yyRuleName)/sizeof(yyRuleName[0])) );
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
                if ((comptime YYTRACKMAXSTACKDEPTH) and (yypParser.yytos - yypParser.yystack) > yypParser.yyhwm) {
                    yypParser.yyhwm += 1;
                    assert(yypParser.yyhwm == yypParser.yytos - yypParser.yystack);
                }
                if (yypParser.yytos >= yypParser.yystackEnd) {
                    if (yyGrowStack(yypParser)) {
                        yyStackOverflow(yypParser);
                        break;
                    }
                }
            }
            yyact = yy_reduce(yypParser, yyruleno, yymajor, yyminor 🍋CTX_PARAM);
        } else if (yyact <= YY_MAX_SHIFTREDUCE) {
            yy_shift(yypParser,yyact, yymajor, yyminor);
            if (comptime !YYNOERRORRECOVERY) {
                yypParser.yyerrcnt -= 1;
            }
            break;
        } else if (yyact == YY_ACCEPT_ACTION) {
            yypParser.yytos -= 1;
            yy_accept(yypParser);
            return;
        } else {
            assert( yyact == YY_ERROR_ACTION );
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
            if (comptime YYERRORSYMBOL) {
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
                if (yypParser.yyerrcnt < 0) {
                    yy_syntax_error(yypParser, yymajor, yyminor);
                }
                yymx = yypParser.yytos[0].major;
                if (yymx == YYERRORSYMBOL || yyerrorhit) {
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
                        yyact = yy_find_reduce_action(yypParser.tos.stateno, YYERRORSYMBOL);
                        if (yyact <= YY_MAX_SHIFTREDUCE) break;
                        yy_pop_parser_stack(yypParser);
                    }
                    if (yypParser.tos <= yypParser.stack or yymajor == 0) {
                        yy_destructor(yypParser, yymajor, &yyminorunion);
                        yy_parse_failed(yypParser);
                        if (comptime !YYNOERRORRECOVERY) {
                            yypParser.yyerrcnt = null;
                        }
                        yymajor = YYNOCODE;
                    } else if (yymx != YYERRORSYMBOL) {
                        yy_shift(yypParser, yyact, YYERRORSYMBOL, yyminor);
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
                yy_syntax_error(yypParser,yymajor, yyminor);
                yy_destructor(yypParser,(YYCODETYPE)yymajor,&yyminorunion);
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
                    yy_syntax_error(yypParser, yymajor, yyminor);
                }
                yypParser.errcnt = 3;
                yy_destructor(yypParser, yymajor, &yyminorunion);
                if( yyendofinput ){
                      yy_parse_failed(yypParser);
                    if (comptime !YYNOERRORRECOVERY) {
                          yypParser->yyerrcnt = -1;
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

