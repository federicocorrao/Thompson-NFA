/*
	thompson.y
	Genera il grafo di un NFA a partire da una espressione regolare.
	
	Commento alla soluzione:
	La costruzione dell'automa pone qualche problema nel caso della concatenazione,
	che sembra essere non banale. Infatti (per definizione) l'algoritmo di Thompson
	prevede l'accorpamento di due stati (rispettivamente finale e iniziale degli 
	automi da concatenare). La concatenazione è il caso in cui sarebbe utile
	poter utilizzare attributi ereditati.
	Dato che Bison (effettuando un parsing bottom-up) non consente l'uso di attributi
	ereditati, "simulare" gli assegnamenti ad attributi ereditati avrebbe richiesto
	l'uso di uno stack ed altre variabili globali. Dopo aver tentato questa strada,
	ho ritenuto che le azioni semantiche fossero totalmente "scorrelate" dalla
	struttura della grammatica scelta; ho in pratica ritenuto che fosse un approccio
	poco elegante.
	
	Quindi ho optato per una soluzione forse più inefficiente ma più semplice:
	1) Utilizzare solo attributi sintetizzati. Ciò mantiene le azioni semantiche
		abbastanza intuitive, ma introduce uno stato superfluo ogni volta che si
		effettua una concatenazione. Le concatenazioni sono effettuate tramite
		epsilon-transizioni (non avviene alcun accorpamento tra stati).
		L'automa prodotto è equivalente
	2) Costruire esplicitamente il grafo dell'automa durante il parsing
	3) Visitare opportunamente il grafo ottenuto (dopo il parsing):
		- La funzione NaiveVisit mostra l'automa prodotto durante il parsing
		 	(gli stati superflui sono indicati in blu)
		- La funzione SmartVisit mostra l'automa corretto secondo l'algoritmo
			di Thompson, accorpa gli stati relativi ad una concatenazione.
	
	Al termine dell'esecuzione vengono generati due file: nfa_naive.pdf e
	nfa_smart.pdf, dai quali è possibile vedere le differenze (ovvero quali
	nodi sono stati accorpati).
	
	Ulteriori considerazioni:
	- La grammatica non presenta ricorsione sinistra, ma non è stato applicato left-factoring
	- La OR è right-associative (non sembra essere un problema)
	- La grammatica non riconosce "a***" - utilizzare "(((a)*)*)*"
	- La gestione del grafo e delle visite non è perfetta (es. free non ancora
		implementato); il tutto è solo per dare un'idea dell'approccio. 
*/

%{
	#include <stdio.h>
	#include <stdlib.h>

/* Gestione Struttura Node e Grafo */
	
	/* 	Indica il tipo di un nodo (edge) ovvero in che circostanza è stato
		creato tale nodo (edge). Utile per colorare gli elementi del grafo
		Nodo (edge) T_PIPE: verde		Indica costruzione con |
		Nodo (edge)	T_STAR: rosso		Indica costruzione con *
		Nodo (edge) T_CHR : grigio		Indica costruzione (Q)---a-->(Q)
		Nodo (edge)	T_SEQ : blu			Indica costruzione con concatenazione
	*/
	typedef enum { T_CHR = 0, T_SEQ = 1, T_PIPE = 2, T_STAR = 3 } NodeType;
	
	typedef struct strNode
	{
		int id;							// Id stato (progressivo, per dot)
		NodeType type;					//  
		struct strNode *next1;			// Edge uscente 1
		struct strNode *next2;			// Edge uscente 2 (max 2 per costruzione)
		char nextlabel;					// Label/Type edges (0 1 2 3 === epsilon, v. NodeType) 
		char visited;					// Flag utilizzato per visita grafo
	}
	Node;
	
	Node*	InitialState	= NULL;		// Stato iniziale NFA (dopo parsing)
	int 	StateCount 		= 1;		// Conteggio stati (per Node.id)
	
	/* Costruttore Nodo */
	Node* New(NodeType type)
	{	
		Node* newNode 		 = (Node*) malloc(sizeof(Node));
		newNode -> id 		 = StateCount++; 
		newNode -> type 	 = type;
		newNode -> nextlabel = 0;		// default T_CHR
		newNode -> next1	 = NULL;
		newNode -> next2	 = NULL;
		newNode -> visited 	 = 0;
		return newNode;
	}
	
%}

/* Informazioni sui Simboli */

%token LETTER
%token PIPE STAR
%token P_OPEN P_CLOSE
%token END
%type  <Value> LETTER		// L'attributo del token LETTER è un char
%type  <NFA>   RE E S K F	// Tutti i non-terminali rappresentano un NFA
							// con stato iniziale e finale (v. %union)
%start RE					// Assioma grammatica

%union
{
	struct
	{
		Node* Initial;
	    Node* Final;
  	}
  	NFA; 
	char Value;
}

%%

/* Parser */

RE	: 	E END
		{ 
			$<NFA>$.Initial = $<NFA>1.Initial;
			$<NFA>$.Final 	= $<NFA>1.Final;
			
			InitialState	= $<NFA>1.Initial;
			return 0;
		}
	;

E 	:	S
		{	/* default action */
			$<NFA>$.Initial = $<NFA>1.Initial;
			$<NFA>$.Final 	= $<NFA>1.Final;
		} 
	|
		S PIPE E
		{
			Node* newInitial = New(T_PIPE);
			Node* newFinal 	 = New(T_PIPE);
			
			newInitial 		-> next1 = $<NFA>1.Initial;
			newInitial 		-> next2 = $<NFA>3.Initial;
			$<NFA>1.Final 	-> next1 = newFinal;
			$<NFA>3.Final 	-> next2 = newFinal;
			
			newInitial    	-> nextlabel = T_PIPE;
			$<NFA>1.Final 	-> nextlabel = T_PIPE;
			$<NFA>3.Final 	-> nextlabel = T_PIPE;
			
			$<NFA>$.Initial = newInitial;
			$<NFA>$.Final	= newFinal;	
		}
	;

S	: 	K
		{	/* default action */
			$<NFA>$.Initial = $<NFA>1.Initial;
			$<NFA>$.Final 	= $<NFA>1.Final;
		} 
	|
		K S
		{	
			$<NFA>1.Final -> next1 = $<NFA>2.Initial; 	// Concatenazione
			
			$<NFA>1.Final -> type	   = T_SEQ; 		// Segnala merge
			$<NFA>1.Final -> nextlabel = T_SEQ;			// (in blu nel grafo)
			
			$<NFA>$.Initial = $<NFA>1.Initial;
			$<NFA>$.Final 	= $<NFA>2.Final;
		}		
	;

K	: 	F
		{	/* default action */
			$<NFA>$.Initial = $<NFA>1.Initial;
			$<NFA>$.Final 	= $<NFA>1.Final;

		}
	|
		F STAR
		{
			Node* newInitial = New(T_STAR);
			Node* newFinal	 = New(T_STAR);
			
			newInitial 		 -> next1 = $<NFA>1.Initial;
			newInitial 		 -> next2 = newFinal;
			$<NFA>1.Final 	 -> next1 = newFinal;
			$<NFA>1.Final 	 -> next2 = $<NFA>1.Initial;
			
			newInitial 	  	-> nextlabel = T_STAR;
			$<NFA>1.Final 	-> nextlabel = T_STAR;
			
			$<NFA>$.Initial = newInitial;
			$<NFA>$.Final	= newFinal;
		}
	;

F	:	P_OPEN E P_CLOSE
		{
			$<NFA>$.Initial = $<NFA>2.Initial;
			$<NFA>$.Final 	= $<NFA>2.Final;
		}
	|
		LETTER
		{
			/* Crea NFA: (newInitial)---LETTER.value-->(newFinal) */
					
			Node* newInitial = New(T_CHR);
			Node* newFinal	 = New(T_CHR);
			
			newInitial 		 -> nextlabel = $<Value>1;
			newInitial 		 -> next1	  = newFinal;
			
			$<NFA>$.Initial = newInitial;
			$<NFA>$.Final	= newFinal;
		}
	;	
	
%%

/* Gestione file dot (nodi, archi, formattazione, etc) */

	FILE* fp;
	
	char *dotbegin = "digraph { \n graph [fontname = \"monospace\"];\n"
					 "node [fontname = \"monospace\"]; \n"
					 "edge [fontname = \"monospace\" fontsize=10]; \n",
		 *dotend   = "}\n";

	void WriteNode	 (Node* node) { fprintf(fp, "\t%d [shape=circle style=filled];\n", node -> id); }	
	void MarkInitial (int nodeId) { fprintf(fp, "\t%d [penwidth=2 peripheries=2]; \n", nodeId); }
	void MarkFinal	 (int nodeId) { fprintf(fp, "\t%d [penwidth=2 peripheries=3]; \n", nodeId); }
	
	void WriteNodeWithColor (Node* node, NodeType type)
	{
		char* color = (type == T_SEQ ) ? "blue" :
					  (type == T_PIPE) ? "green":
					  (type == T_STAR) ? "red"  :
					  					 "grey" ;
		fprintf(fp, "\t%d [shape=circle style=filled, fillcolor=%s];\n",
			node -> id, color);
	}	
	
	void WriteEdge(int state1, int state2, char* label, NodeType type)
	{
		char* color = (type == T_SEQ ) ? "blue" :
					  (type == T_PIPE) ? "green":
					  (type == T_STAR) ? "red"  :
					  					 "black";  					 
		fprintf(fp, "\t\t%d -> %d [label=\"%s\" color=%s fontcolor=%s];\n",
			state1, state2, label, color, color);
	}

	void ResetVisited(Node*);

	/*	Prepara filename e invoca la funzione di visita desiderata
	*/
	void GenerateDotCode(Node* start, char* filename, void (*visitFunction)(Node*))
	{
		fp = fopen(filename, "w");			// Apertura/creazione file
		fputs(dotbegin, fp);				// "digraph { ..." etc
		(*visitFunction)(start);			// Invoca visita
		ResetVisited(start);				// Reset flag visited
		MarkInitial(start -> id);			// Marca stato iniziale
		fputs(dotend, fp);					// "}"
		fclose(fp);							// Chiusura file
	}


/* Funzioni di visita grafo */

	/* 	Reset flag visited nodi grafo.
		Nota: Assume che tutti i nodi abbiano visited = 1.
			  Ciò non vale dopo SmartVisit().
	*/
	void ResetVisited(Node* node)
	{
		if(node == NULL || node -> visited == 0) return;
		node -> visited = 0;
		ResetVisited(node -> next1);
		ResetVisited(node -> next2);
	}

	char epsilon[] = "&epsilon;";
	char letter[]  = "?";
	
	/*	NaiveVisit
		Visita il grafo, disegna tutti i nodi/archi e li colora opportunamente
		(il colore indica in quale regola un nodo è stato creato). In blu sono
		evidenziati i nodi/archi superflui (da omettere, secondo l'alogoritmo di
		Thompson).
	*/
	void NaiveVisit(Node* node)
	{
		if(node == NULL || node -> visited == 1) return;
		
		WriteNodeWithColor(node, node -> type);
		node -> visited = 1;
		
		char* label = (node -> nextlabel <= T_STAR) ? epsilon :
			(letter[0] = node -> nextlabel, letter);
		
		if(node -> next1)
			WriteEdge(node -> id, node -> next1 -> id, label, node -> nextlabel),
			NaiveVisit(node -> next1);
			
		if(node -> next2)
			WriteEdge(node -> id, node -> next2 -> id, label, node -> nextlabel),
			NaiveVisit(node -> next2);
		
		if(node -> next1 == NULL && node -> next2 == NULL)
			MarkFinal(node -> id); // Marca stato finale
	}

	/*	SmartVisit
		Utilizza Node.type per omettere i nodi/archi con tipo T_SEQ (in blu);
		accorpa lo stato finale e iniziale di due automi "in sequenza".
		Vengono colorati solo gli edge.
		Nota: codice migliorabile, non molto pulito, ma funziona (e rende l'idea).
	*/
	void SmartVisit(Node* node)
	{
		if(node == NULL || node -> visited == 1) return;
		
		WriteNode(node);		
		node -> visited = 1;
		
		char* label = (node -> nextlabel <= T_STAR) ? epsilon :
			(letter[0] = node -> nextlabel, letter);
		
		if(node -> next1)
		{
			if(node -> next1 -> type == T_SEQ)
			{
				WriteEdge(node -> id, node -> next1 -> next1 -> id, label, node -> nextlabel);  // edge verso next 
				node -> next1 -> id = node -> next1 -> next1 -> id; 							// merge		
				node -> next1 = node -> next1 -> next1;											// skip visit 
			}
			else WriteEdge(node -> id, node -> next1 -> id, label, node -> nextlabel);			
			SmartVisit(node -> next1);
		}
		if(node -> next2)																		// idem
		{
			if(node -> next2 -> type == T_SEQ)
			{
				WriteEdge(node -> id, node -> next2 -> next1 -> id, label, node -> nextlabel);	
				node -> next2 -> id = node -> next2 -> next1 -> id;
				node -> next2 = node -> next2 -> next1;
			}
			else WriteEdge(node -> id, node -> next2 -> id, label, node -> nextlabel);
			SmartVisit(node -> next2);
		}
		if(node -> next1 == NULL && node -> next2 == NULL)
			MarkFinal(node -> id); // Marca stato finale 
	}


/* Main */

	#include "lex.yy.c"

	int main(int argc, char** argv)
	{
		if(argc == 1)
		{
			printf("Regexp > ");
			if(!yyparse())
			{
				printf("Regexp successfully parsed!\n");
				
				/* Note:
				- SmartVisit modifica i puntatori del grafo.
					NaiveVisit deve essere chiamata prima.
				- Free non ancora implementato (non un grande problema
					visto che il programma sta per terminare).
				*/
				
				GenerateDotCode(InitialState, "nfa_naive.dot.txt", &NaiveVisit);
				system("dot nfa_naive.dot.txt -Tpdf -o nfa_naive.pdf");
				
				GenerateDotCode(InitialState, "nfa_smart.dot.txt", &SmartVisit);
				system("dot nfa_smart.dot.txt -Tpdf -o nfa_smart.pdf");
				
				/* todo free graph and loop */		
			}
		}
		else { /* */ }
	 }

	int yyerror(char* s) { printf("yyparse error: %s\n", s); return 0; }
		
/* */


