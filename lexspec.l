%option dotall unicode
lower       [a-z]
upper       [A-Z]
digit       [0-9]
alpha       ({lower}|{upper}|_)
alnum       ({alpha}|{digit})
letter      ({alpha}|{upper})
lower_ident ({lower}|_)({alnum}|')*
ident       ({letter}|_)({alnum}|')*
%{
#include <iomanip>
#include "lex.hpp"
#define DUMP(kind) kind(cnum, lineno(), 1 + columno(), lineno_end(), 2 + columno_end(), text())
%}

%class{
int level = 0;
size_t cnum = 0;
const std::string filename;
%}
%option ctorarg="const std::string& filename"
%option ctorinit="filename(filename)"

%x COMMENT

%%
"+."|"-."|"*."|"/."|"+"|"-"|"*"|"/"|"<>"|"<="|">="|"<-"|"<"|">"|"="|"("|")"|"."|";;"|";"|","
                                            out() << DUMP(Op) << '\n'; cnum += wsize();
{digit}+                                    out() << DUMP(I) << '\n'; cnum += wsize();
{digit}+(\.{digit}*)?([eE][+-]?{digit}+)?   out() << DUMP(F) << '\n'; cnum += wsize();
"true"|"false"                              out() << DUMP(B) << '\n'; cnum += wsize();
{lower_ident}                               out() << DUMP(W) << '\n'; cnum += wsize();
"Array"                                     out() << DUMP(W) << '\n'; cnum += wsize();
"(*"                                        level = 1; start(COMMENT); cnum += 2;

<COMMENT> {
"(*"                                        level++; cnum += 2;
"*)"                                        cnum+=2; if (--level == 0) start(INITIAL);
\X                                          cnum++; // skip everything else

<<EOF>>                                     std::cerr << filename << ":" << lineno() << ":" << columno() + 1 << ": " << "unterminated comment\n";
                                            std::cerr << std::setw(5) << lineno() << " |"; std::wcerr << matcher().wline() << '\n';
                                            std::cerr << std::string(5 + 2 + columno(), ' ') << "^\n";
                                            return 1;

.                                           std::cerr << filename << ":" << lineno() << ":" << columno() + 1 << ": " << "unknown character " << text() << '\n';
                                            std::cerr << std::setw(5) << lineno() << " |"; std::wcerr << matcher().wline() << '\n';
                                            std::cerr << std::string(5 + 2 + columno(), ' ') << "^\n";
                                            return 1;
}
\s+                                         cnum += wsize(); // skip everything else
<<EOF>>                                     out() << Eof(cnum, lineno(), 1 + columno()) <<'\n'; return 0;
.                                           std::cerr << filename << ":" << lineno() << ":" << columno() + 1 << ": " << "unknown character " << text() << '\n';
                                            std::cerr << std::setw(5) << lineno() << " |"; std::wcerr << matcher().wline() << '\n';
                                            std::cerr << std::string(5 + 2 + columno(), ' ') << "^\n";
                                            return 1;
%%