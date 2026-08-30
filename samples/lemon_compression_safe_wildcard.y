%name Parse
%token_type {int}
%extra_argument {int *result}
%include {
#include <assert.h>
#include <stdlib.h>
}
%syntax_error { *result = -1; }
%parse_accept { *result = 1; }
%wildcard W.

start ::= P leaf D.
start ::= Q leaf W.
leaf ::= C.

%code {
static int run(int prefix, int suffix){
  int result = 0;
  void *parser = ParseAlloc(malloc);
  assert(parser != 0);
  Parse(parser, prefix, 0, &result);
  Parse(parser, C, 0, &result);
  Parse(parser, suffix, 0, &result);
  Parse(parser, 0, 0, &result);
  ParseFree(parser, free);
  return result;
}

int main(void){
%ifdef COMPRESSION_EXPECTED
  if( YYNSTATE!=7 || YY_ACTTAB_COUNT!=11 ) return 1;
%else
  if( YYNSTATE!=8 || YY_ACTTAB_COUNT!=13 ) return 1;
%endif
  return run(P, D)!=1 || run(Q, D)!=1;
}
}
