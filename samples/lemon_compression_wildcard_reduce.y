%name Parse
%token_type {int}
%extra_argument {int *result}
%include {
#include <assert.h>
#include <stdlib.h>
}
%syntax_error { if (*result == 0) *result = -1; }
%parse_accept { if (*result == 0) *result = 1; }
%wildcard W.

start ::= P aa D.
start ::= P bb W Z.
start ::= Q aa E.
start ::= Q bb W Z.
aa ::= C.
bb ::= C.

%code {
static int run(void){
  int result = 0;
  void *parser = ParseAlloc(malloc);
  assert(parser != 0);
  Parse(parser, P, 0, &result);
  Parse(parser, C, 0, &result);
  Parse(parser, D, 0, &result);
  Parse(parser, 0, 0, &result);
  ParseFree(parser, free);
  return result;
}

int main(void){
  return run() != 1;
}
}
