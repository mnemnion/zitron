%include {
} // end %include

%name pik_parser
%token_prefix T_
%token_type {PToken}
%extra_context {Pik *p}

%fallback ID EDGEPT.

// precedence rules.
%left OF.
%left PLUS MINUS.
%left STAR SLASH PERCENT.
%right UMINUS.

%type statement_list {PList*}
%destructor statement_list {pik_elist_free(p,$$);}
%type statement {PObj*}
%destructor statement {pik_elem_free(p,$$);}
%type unnamed_statement {PObj*}
%destructor unnamed_statement {pik_elem_free(p,$$);}
%type basetype {PObj*}
%destructor basetype {pik_elem_free(p,$$);}
%type expr {PNum}
%type numproperty {PToken}
%type edge {PToken}
%type direction {PToken}
%type dashproperty {PToken}
%type colorproperty {PToken}
%type locproperty {PToken}
%type position {PPoint}
%type place {PPoint}
%type object {PObj*}
%type objectname {PObj*}
%type nth {PToken}
%type textposition {short int}
%type rvalue {PNum}
%type lvalue {PToken}
%type even {PToken}
%type relexpr {PRel}
%type optrelexpr {PRel}

%syntax_error {
  if( TOKEN.z && TOKEN.z[0] ){
    pik_error(p, &TOKEN, "syntax error");
  }else{
    pik_error(p, 0, "syntax error");
  }
  UNUSED_PARAMETER(yymajor);
}
%stack_overflow {
  pik_error(p, 0, "parser stack overflow");
}

document ::= statement_list(X).  {pik_render(p,X);}


statement_list(A) ::= statement(X).   { A = pik_elist_append(p,0,X); }
statement_list(A) ::= statement_list(B) EOL statement(X).
                      { A = pik_elist_append(p,B,X); }


statement(A) ::= .   { A = 0; }
statement(A) ::= direction(D).  { pik_set_direction(p,D.eCode);  A=0; }
statement(A) ::= lvalue(N) ASSIGN(OP) rvalue(X). {pik_set_var(p,&N,X,&OP); A=0;}
statement(A) ::= PLACENAME(N) COLON unnamed_statement(X).
               { A = X;  pik_elem_setname(p,X,&N); }
statement(A) ::= PLACENAME(N) COLON position(P).
               { A = pik_elem_new(p,0,0,0);
                 if(A){ A->ptAt = P; pik_elem_setname(p,A,&N); }}
statement(A) ::= TITLE STRING(S).{ pik_set_title(p, &S, 0); A=0; }
statement(A) ::= LABEL STRING(S). { pik_set_title(p, &S, 1); A=0; }
statement(A) ::= DESCRIBE STRING(S). { pik_set_description(p, &S); A=0; }
statement(A) ::= unnamed_statement(X).  {A = X;}
statement(A) ::= print prlist.  {pik_append(p,"<br>\n",5); A=0;}

// assert() statements are undocumented and are intended for testing and
// debugging use only.  If the equality comparison of the assert() fails
// then an error message is generated.
statement(A) ::= ASSERT LP expr(X) EQ(OP) expr(Y) RP. {A=pik_assert(p,X,&OP,Y);}
statement(A) ::= ASSERT LP position(X) EQ(OP) position(Y) RP.
                                          {A=pik_position_assert(p,&X,&OP,&Y);}
statement(A) ::= DEFINE ID(ID) CODEBLOCK(C).  {A=0; pik_add_macro(p,&ID,&C);}

lvalue(A) ::= ID(A).
lvalue(A) ::= FILL(A).
lvalue(A) ::= COLOR(A).
lvalue(A) ::= TEXTCOLOR(A).
lvalue(A) ::= THICKNESS(A).

// PLACENAME might actually be a color name (ex: DarkBlue).  But we
// cannot make it part of expr due to parsing ambiguities.  The
// rvalue non-terminal means "general expression or a colorname"
rvalue(A) ::= expr(A).
rvalue(A) ::= PLACENAME(C).  {A = pik_lookup_color(p,&C);}

print ::= PRINT.
prlist ::= pritem.
prlist ::= prlist prsep pritem.
pritem ::= FILL(X).        {pik_append_num(p,"",pik_value(p,X.z,X.n,0));}
pritem ::= COLOR(X).       {pik_append_num(p,"",pik_value(p,X.z,X.n,0));}
pritem ::= THICKNESS(X).   {pik_append_num(p,"",pik_value(p,X.z,X.n,0));}
pritem ::= rvalue(X).      {pik_append_num(p,"",X);}
pritem ::= STRING(S). {pik_append_text(p,S.z+1,S.n-2,0);}
prsep  ::= COMMA. {pik_append(p, " ", 1);}

unnamed_statement(A) ::= basetype(X) attribute_list.
                          {A = X; pik_after_adding_attributes(p,A);}

basetype(A) ::= CLASSNAME(N).            {A = pik_elem_new(p,&N,0,0); }
basetype(A) ::= STRING(N) textposition(P).
                            {N.eCode = P; A = pik_elem_new(p,0,&N,0); }
basetype(A) ::= LB savelist(L) statement_list(X) RB(E).
      { p->list = L; A = pik_elem_new(p,0,0,X); if(A) A->errTok = E; }

%type savelist {PList*}
// No destructor required as this same PList is also held by
// an "statement" non-terminal deeper on the stack.
savelist(A) ::= .   {A = p->list; p->list = 0;}

direction(A) ::= UP(A).
direction(A) ::= DOWN(A).
direction(A) ::= LEFT(A).
direction(A) ::= RIGHT(A).

relexpr(A) ::= expr(B).             {A.rAbs = B; A.rRel = 0;}
relexpr(A) ::= expr(B) PERCENT.     {A.rAbs = 0; A.rRel = B/100;}
optrelexpr(A) ::= relexpr(A).
optrelexpr(A) ::= .                 {A.rAbs = 0; A.rRel = 1.0;}

attribute_list ::= relexpr(X) alist.    {pik_add_direction(p,0,&X);}
attribute_list ::= alist.
alist ::=.
alist ::= alist attribute.
attribute ::= numproperty(P) relexpr(X).     { pik_set_numprop(p,&P,&X); }
attribute ::= dashproperty(P) expr(X).       { pik_set_dashed(p,&P,&X); }
attribute ::= dashproperty(P).               { pik_set_dashed(p,&P,0);  }
attribute ::= colorproperty(P) rvalue(X).    { pik_set_clrprop(p,&P,X); }
attribute ::= go direction(D) optrelexpr(X). { pik_add_direction(p,&D,&X);}
attribute ::= go direction(D) even position(P). {pik_evenwith(p,&D,&P);}
attribute ::= CLASS ID(C). {pik_set_xml_class(p, &C);}
attribute ::= CLASS XML_CLASSES(C). {pik_set_xml_classes(p, &C);}
attribute ::= CLOSE(E).             { pik_close_path(p,&E); }
attribute ::= CHOP.                 { p->cur->bChop = 1; }
attribute ::= FROM(T) position(X).  { pik_set_from(p,p->cur,&T,&X); }
attribute ::= TO(T) position(X).    { pik_add_to(p,p->cur,&T,&X); }
attribute ::= THEN(T).              { pik_then(p, &T, p->cur); }
attribute ::= THEN(E) optrelexpr(D) HEADING(H) expr(A).
                                                {pik_move_hdg(p,&D,&H,A,0,&E);}
attribute ::= THEN(E) optrelexpr(D) EDGEPT(C).  {pik_move_hdg(p,&D,0,0,&C,&E);}
attribute ::= GO(E) optrelexpr(D) HEADING(H) expr(A).
                                                {pik_move_hdg(p,&D,&H,A,0,&E);}
attribute ::= GO(E) optrelexpr(D) EDGEPT(C).    {pik_move_hdg(p,&D,0,0,&C,&E);}
attribute ::= boolproperty.
attribute ::= AT(A) position(P).                    { pik_set_at(p,0,&P,&A); }
attribute ::= WITH withclause.
attribute ::= SAME(E).                          {pik_same(p,0,&E);}
attribute ::= SAME(E) AS object(X).             {pik_same(p,X,&E);}
attribute ::= STRING(T) textposition(P).        {pik_add_txt(p,&T,P);}
attribute ::= FIT(E).                           {pik_size_to_fit(p,&E,3); }
attribute ::= BEHIND object(X).                 {pik_behind(p,X);}

go ::= GO.
go ::= .

even ::= UNTIL EVEN WITH.
even ::= EVEN WITH.

withclause ::=  DOT_E edge(E) AT(A) position(P).{ pik_set_at(p,&E,&P,&A); }
withclause ::=  edge(E) AT(A) position(P).      { pik_set_at(p,&E,&P,&A); }

// Properties that require an argument
numproperty(A) ::= HEIGHT|WIDTH|RADIUS|DIAMETER|THICKNESS(P).  {A = P;}

// Properties with optional arguments
dashproperty(A) ::= DOTTED(A).
dashproperty(A) ::= DASHED(A).

// Color properties
colorproperty(A) ::= FILL(A).
colorproperty(A) ::= COLOR(A).
colorproperty(A) ::= TEXTCOLOR(A).

// Properties with no argument
boolproperty ::= CW.          {p->cur->cw = 1;}
boolproperty ::= CCW.         {p->cur->cw = 0;}
boolproperty ::= LARROW.      {p->cur->larrow=1; p->cur->rarrow=0; }
boolproperty ::= RARROW.      {p->cur->larrow=0; p->cur->rarrow=1; }
boolproperty ::= LRARROW.     {p->cur->larrow=1; p->cur->rarrow=1; }
boolproperty ::= INVIS.       {p->cur->sw = -0.00001;}
boolproperty ::= THICK.       {p->cur->sw *= 1.5;}
boolproperty ::= THIN.        {p->cur->sw *= 0.67;}
boolproperty ::= SOLID.       {p->cur->sw = pik_value(p,"thickness",9,0);
                               p->cur->dotted = p->cur->dashed = 0.0;}

textposition(A) ::= .   {A = 0;}
textposition(A) ::= textposition(B)
   CENTER|LJUST|RJUST|ABOVE|BELOW|ITALIC|BOLD|MONO|ALIGNED|BIG|SMALL(F).
                        {A = (short int)pik_text_position(B,&F);}


position(A) ::= expr(X) COMMA expr(Y).                {A.x=X; A.y=Y;}
position(A) ::= place(A).
position(A) ::= place(B) PLUS expr(X) COMMA expr(Y).  {A.x=B.x+X; A.y=B.y+Y;}
position(A) ::= place(B) MINUS expr(X) COMMA expr(Y). {A.x=B.x-X; A.y=B.y-Y;}
position(A) ::= place(B) PLUS LP expr(X) COMMA expr(Y) RP.
                                                      {A.x=B.x+X; A.y=B.y+Y;}
position(A) ::= place(B) MINUS LP expr(X) COMMA expr(Y) RP.
                                                      {A.x=B.x-X; A.y=B.y-Y;}
position(A) ::= LP position(X) COMMA position(Y) RP.  {A.x=X.x; A.y=Y.y;}
position(A) ::= LP position(X) RP.                    {A=X;}
position(A) ::= expr(X) between position(P1) AND position(P2).
                                       {A = pik_position_between(X,P1,P2);}
position(A) ::= expr(X) LT position(P1) COMMA position(P2) GT.
                                       {A = pik_position_between(X,P1,P2);}
position(A) ::= expr(X) ABOVE position(B).    {A=B; A.y += X;}
position(A) ::= expr(X) BELOW position(B).    {A=B; A.y -= X;}
position(A) ::= expr(X) LEFT OF position(B).  {A=B; A.x -= X;}
position(A) ::= expr(X) RIGHT OF position(B). {A=B; A.x += X;}
position(A) ::= expr(D) ON HEADING EDGEPT(E) OF position(P).
                                        {A = pik_position_at_hdg(D,&E,P);}
position(A) ::= expr(D) HEADING EDGEPT(E) OF position(P).
                                        {A = pik_position_at_hdg(D,&E,P);}
position(A) ::= expr(D) EDGEPT(E) OF position(P).
                                        {A = pik_position_at_hdg(D,&E,P);}
position(A) ::= expr(D) ON HEADING expr(G) FROM position(P).
                                        {A = pik_position_at_angle(D,G,P);}
position(A) ::= expr(D) HEADING expr(G) FROM position(P).
                                        {A = pik_position_at_angle(D,G,P);}

between ::= WAY BETWEEN.
between ::= BETWEEN.
between ::= OF THE WAY BETWEEN.

// place2 is the same as place, but excludes the forms like
// "RIGHT of object" to avoid a parsing ambiguity with "place .x"
// and "place .y" expressions
%type place2 {PPoint}

place(A) ::= place2(A).
place(A) ::= edge(X) OF object(O).           {A = pik_place_of_elem(p,O,&X);}
place2(A) ::= object(O).                     {A = pik_place_of_elem(p,O,0);}
place2(A) ::= object(O) DOT_E edge(X).       {A = pik_place_of_elem(p,O,&X);}
place2(A) ::= NTH(N) VERTEX(E) OF object(X). {A = pik_nth_vertex(p,&N,&E,X);}

edge(A) ::= CENTER(A).
edge(A) ::= EDGEPT(A).
edge(A) ::= TOP(A).
edge(A) ::= BOTTOM(A).
edge(A) ::= START(A).
edge(A) ::= END(A).
edge(A) ::= RIGHT(A).
edge(A) ::= LEFT(A).

object(A) ::= objectname(A).
object(A) ::= nth(N).                     {A = pik_find_nth(p,0,&N);}
object(A) ::= nth(N) OF|IN object(B).     {A = pik_find_nth(p,B,&N);}

objectname(A) ::= THIS.                   {A = p->cur;}
objectname(A) ::= PLACENAME(N).           {A = pik_find_byname(p,0,&N);}
objectname(A) ::= objectname(B) DOT_U PLACENAME(N).
                                          {A = pik_find_byname(p,B,&N);}

nth(A) ::= NTH(N) CLASSNAME(ID).      {A=ID; A.eCode = pik_nth_value(p,&N); }
nth(A) ::= NTH(N) LAST CLASSNAME(ID). {A=ID; A.eCode = -pik_nth_value(p,&N); }
nth(A) ::= LAST CLASSNAME(ID).        {A=ID; A.eCode = -1;}
nth(A) ::= LAST(ID).                  {A=ID; A.eCode = -1;}
nth(A) ::= NTH(N) LB(ID) RB.          {A=ID; A.eCode = pik_nth_value(p,&N);}
nth(A) ::= NTH(N) LAST LB(ID) RB.     {A=ID; A.eCode = -pik_nth_value(p,&N);}
nth(A) ::= LAST LB(ID) RB.            {A=ID; A.eCode = -1; }

expr(A) ::= expr(X) PLUS expr(Y).                 {A=X+Y;}
expr(A) ::= expr(X) MINUS expr(Y).                {A=X-Y;}
expr(A) ::= expr(X) STAR expr(Y).                 {A=X*Y;}
expr(A) ::= expr(X) SLASH(E) expr(Y).             {
  if( Y==0.0 ){ pik_error(p, &E, "division by zero"); A = 0.0; }
  else{ A = X/Y; }
}
expr(A) ::= MINUS expr(X). [UMINUS]               {A=-X;}
expr(A) ::= PLUS expr(X). [UMINUS]                {A=X;}
expr(A) ::= LP expr(X) RP.                        {A=X;}
expr(A) ::= LP FILL|COLOR|TEXTCOLOR|THICKNESS(X) RP. {A=pik_get_var(p,&X);}
expr(A) ::= NUMBER(N).                            {A=pik_atof(&N);}
expr(A) ::= ID(N).                                {A=pik_get_var(p,&N);}
expr(A) ::= FUNC1(F) LP expr(X) RP.               {A = pik_func(p,&F,X,0.0);}
expr(A) ::= FUNC2(F) LP expr(X) COMMA expr(Y) RP. {A = pik_func(p,&F,X,Y);}
expr(A) ::= DIST LP position(X) COMMA position(Y) RP. {A = pik_dist(&X,&Y);}
expr(A) ::= place2(B) DOT_XY X.                   {A = B.x;}
expr(A) ::= place2(B) DOT_XY Y.                   {A = B.y;}
expr(A) ::= object(B) DOT_L numproperty(P).       {A=pik_property_of(B,&P);}
expr(A) ::= object(B) DOT_L dashproperty(P).      {A=pik_property_of(B,&P);}
expr(A) ::= object(B) DOT_L colorproperty(P).     {A=pik_property_of(B,&P);}


%code {
} // end %code
