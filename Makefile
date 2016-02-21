all: thompson

thompson:
	flex thompson.l
	bison thompson.y -v
	gcc -o thompson thompson.tab.c

clear:
	rm -f thompson.output thompson.tab.c lex.yy.c
