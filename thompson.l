
%option noyywrap

%{
	#include <stdio.h>
%}

letter		[a-zA-Z0-9]
star		"*"
pipe		"|"
popen		"("
pclose		")"

%%

[ \t]		{ /* ignore whitespace */ }

{letter}	{ yylval.Value = yytext[0]; return LETTER;	}
{star} 		{	 				 		return STAR; 	}
{pipe}		{   					 	return PIPE; 	}
{popen}		{  					 		return P_OPEN;	}
{pclose}	{ 	 				 		return P_CLOSE;	}

[\n\r]		{ return END; }

%%

