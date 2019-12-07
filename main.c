 /*
* Universidad Nacional Autónoma de México
* Facultad de Ingeniería
* @Date: Diciembre 9, 2019
* @Author:
*       Landín Matínez Uri Raquel
*       Sánchez Escobar Fernando
*       Torres Galván José Antonio
*       Valdes Vargas Rocio Monserrat
* @Description: Programa que hace el análisis sintáctico y semántico. Recibe las clases léxicas del scanner y junto con este determina si el código de entrada es aceptado o no 
*/

%{
#include <stdio.h>
#include <stdlib.h>
#include "tablaSimbolos.h"
#include "tablaTipos.h"
#include "tablaDirecciones.h"
void yyerror(char* msg);
extern int yylex();
extern int yylineno;

/* ------ Variables Globales ------ */
int tipoGbl;
int dirGbl;
int funcTipo;
typestack *stackTT;
symstack *stackTS;
stackDir stackDirr = NULL;
//code codigoGbl;
//cadTable stringT;
//list funcReturn;
//label L, L1;
//index I;
%}

/* Estructuras */
%union{
  //int tipo;
  struct _num{
    int tipo;
    union {
      int eval;
      float rval;
      double dval;
      char cval;
    }
  }num;

  struct _list{
    union{
      int ival; //para 
      char *cvar;
    }
    struct _list *next;
  }list;

  struct{
    int tipo;
    int dimension;
  } tipo;
}

/* Terminales */
%token<sval> REGISTRO /* Otro tipo de tipos*/
%token<sval> INICIO
%token<sval> FIN
%token<sval> TIPO /*o base?*/
%token<sval> BASE
%token<sval> NUM /*<numero> con otra estrcutrura?*/
%token<sval> ID
%token<sval> COMA
%token<sval> PUNTO
%token<sval> FUNC

%token<sval> ENT //Tipo entero
%token<sval> REAL //Tipo real
%token<sval> DREAL //Tipo doble real
%token<sval> CAR //Tipo caracter
%token<sval> SIN //Tipo sin retorno
%token<sval> GT //Mayor que
%token<sval> LT //Menor que
%token<sval> GE //Mayor igual que
%token<sval> LE //Menor igual que
%token<sval> EQ //Igual que
%token<sval> NE //Diferente que

%token<sval> SI
%token<sval> SINO
%token<sval> ENTONCES
%token<sval> MIENTRAS
%token<sval> MIENTRASQUE
%token<sval> HACER
%token<sval> ASIGNA /*:=*/
%token<sval> ESCRIBIR
%token<sval> LEER
%token<sval> DEVOLVER
%token<sval> TERMINAR
%token<sval> OO /*precedencia?*/
%token<sval> YY /*precendencia?*/
%token<sval> NO
%token<sval> VERDADERO /*precedencia?*/
%token<sval> FALSO /*precedencia?*/
%token<sval> COMMENT
%token<sval> SPACE

/* operaciones? */
%token<sval> CADENA
%token<sval> CARACTER
%token<sval> NL /*salto de linea*/

/* Asociatividad y precedencia */
%left MAS RES
%left MOD
%left DIV MUL

%nonassoc LPAR RPAR LCOR RCOR

/* Simbolos no terminales */
%type<sval> declaraciones tipo_arreglo lista_var funciones argumentos lista_arg arg tipo_arg param_arr sentencias sentencia expresion_booleana relacional expresion variable arreglo parametros lista_param base

%type<tipo> tipo tipo_registro 

/* Simbolo inicial */
%start programa

%%

programa: declaraciones NL funciones {
  //dir=0;//Esto ya es una variable global
  //typestack *stackTT=crearTypeStack();
  //*stackTT=crearTypeStack();
  //symstack *stackTS=crearSymStack();
  //*stackTS=crearSymStack();
  //symtab *ts=crearSymTab();
  //typetab *tt=crearTypeTab();
  //insertarSymTab(ts,stackTS);
  //insertarTypeTab(tt,stackTT);
  //Tabla de cadenas
  //Crear pila Direcciones dirstack *stackDir=crearDirStack();
  dirGbl = 0; //Igualamos a 0 la variable global de dirección
  stackTT=crearTypeStack(); //Crear apuntador a pila de tipos
  stackTS=crearSymStack(); //Crear apuntador a pila de símbolos
  symtab *ts=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
  typetab *tt=crearTypeTab(); //Creamos una apuntador a una tabla de tipos
  insertarSymTab(ts,stackTS); //Insertamos en la pila la tabla de simbolos
  insertarTypeTab(tt,stackTT); //Insertamos en la pila la tabla de tipos
}
;

declaraciones: /*vacia*/ {}
	     | tipo lista_var NL declaraciones {
         //tipoGbl=tipo.tipo
         tipoGbl = $1.tipo;
         } //type y base son estructuras??
	     | tipo_registro lista_var NL declaraciones {
         //tipoGbl=tipo_registro.tipo
         tipoGbl = $1.tipo;
         }

tipo_registro: REGISTRO NL INICIO declaraciones NL FIN {
  //ts=crearSymTab();
  //tt=crearTypeTab();
  /* Pila Direcciones se le hace push, se le pasa la pila y la dirección que hay que meter
  pushStackDir(dir,stackDir);
  */ //Pero no se pone solo la dirección ya que solo es una pila para las direcciones?
  /*dir=0;
  insertarSymTab(ts,stackTS);
  insertarTypeTab(tt,stackTT);
  dir=popStackDir(stackDir);
  typetab *tt1=sacarTypeTab(stackTT);
  symmtab *temp1=getCimaSym(stackTS);
  //temp1.setTT(tt1);
  setTT(getCimaSym(stackTS),sacarTypeTab(stackTT)); //?? Mejor
  symtab *ts1=sacarSymTab(stackTS);
  dir=popStackDir(stackDir);
  typetab temp2=getCimaType(stackTT);
  type=insertarTipo(getCimaType(stackTT),"registro",0,sacarSymTab(stackTS)) //Verificar*/
  symtab *ts=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
  typetab *tt=crearTypeTab(); //Creamos una apuntador a una tabla de tipos
  dirGbl=0;  //Igualamos a 0 la variable global de dirección
  pushDir(&stackDirr,dirGbl); //Insertamos en nuestra tabla de direcciones la dirección iniciada en 0
  insertarTypeTab(tt,stackTT); //Insertamos en la pila la tabla de tipos
  insertarSymTab(ts,stackTS); //Insertamos en la pila la tabla de simbolos
  dirGbl = popDir(&stackDirr);
  typetab *tt1=crearTypeTab(); //Creamos una apuntador a una tabla de tipos temporal
  tt1 = sacarTypeTab(stackTT);
  //StackTS.getCima().setTT(tt1)//No se qué sea set, pienso que puede ser "insertar" en la tabla de símbolos
  symtab *ts1=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
  ts1 = sacarSymTab(stackTS);
  dirGbl = popDir(&stackDirr);
  //tipoGbl = insertarTipo(getCimaType(typestack *ts),) //<-- No sé cómo hacer esto
}
;

tipo: base tipo_arreglo {
           baseGbl=$1.tipo;
           $$.tipo=$2.tipo;
}
;
base:  ENT{$$.tipo = 0;}
      |REAL{$$.tipo = 1;}
      |DREAL{$$.tipo = 2;}
      |CAR{$$.tipo = 3;}
      |SIN{$$.tipo = 4;}
;
tipo_arreglo: LCOR NUM RCOR tipo_arreglo {
  if (NUM.tipo==ent && NUM.val>0){
    tipo_arreglo.tipo=insertarTipo(getCimaType(stackTT),"array",NUM.val,tipo_arreglo.tipo) //Verificar
  }else{
    printf("ERROR: El indice debe ser un número entero y mayor que 0");
  } 
}
	    | /*vacia*/ {tipo_arreglo.tipo=base}
;

lista_var: lista_var COMA ID {
  /*if (buscar(getCimaSym(stackTS),ID)== -1){
    symbol *sym=crearSymbol(ID.val,tipo,dir,"var"); //dir? //Definir var tipo?
    insertar(getCimaSym(stackTS), sym);
    dir=dir+getTam(getCimaType(stackTT),ID);
  }
  else{
    printf("ERROR: Este identificador ya fue declarado");
  }*/
  if(buscar(getCimaSym(stackTS),$3.sval)==-1){
          symbol *s=crearSymbol($3.sval, tipoGbl, dirGbl, 0);
          insertar(getCimaSym(stackTS),s);
          dirGbl += getTam(getCimaType(stackTT),tipoGbl);
        }
  else
          yyerror("El identificador ya fue declarado");
}
	 | ID { //IGUAL AL ANTERIOR??
     if (buscar(getCimaSym(stackTS),ID)== -1){
    symbol *sym=crearSymbol(ID.val,tipo,dir,"var"); //dir? //Definir var tipo?
    insertar(getCimaSym(stackTS), sym);
    dir=dir+getTam(getCimaType(stackTT),ID);
  }
  else{
    printf("ERROR: Este identificador ya fue declarado");
  }
   }
;

funciones: FUNC tipo ID LPAR argumentos RPAR INICIO NL declaraciones sentencias NL FIN NL funciones {
    if (buscar(getFondoSym(stackTS),ID.val)== -1){
    symbol *sym=crearSymbol(ID.val,tipo,"-","func"); //-? //Definir var tipo?
    insertar(getFondoSym(stackTS), sym);
    pushStackDir(dir,stackDir);
    FuncType=tipo.tipo;
    FuncReturn=false;
    dir=0;
    insertarTypeTab(tt,stackTT);
    insertarSymTab(ts,stackTS);
    dir=popStackDir(stackDir);
    //add_cuad(code, 0 label 0 , −, −, id.lexval)
    L=newLabel();
    backpatch(code,sentencias.next,L);
    //add_cuad(code,'label',-,-,L)
    sacarTypeTab(stackTT);
    sacarSymTab(stackTS);
    dir=popStackDir(stackDir);
    StackT S.getCima().addArgs(id.lexval, argumentos.lista)
    if (tipo.tipo != SIN && FuncReturn == false){
      Error(la función no tiene valor de retorno)
    } 
  }
  else{
    printf("ERROR: Este identificador ya fue declarado");
  }
}
	 | /*vacia*/{}
;

argumentos: lista_arg {argumentos.list=lista.arg.list;} //Hacer un for para comparar cada uno de los elementos?
	  | SIN {argumentos.list.next=NULL;} /*Tengo duda aqui*/
;

lista_arg: lista_arg arg {
  lista_arg.list=lista_arg1.list;
  lista_arg.list.add(arg.tipo);
  }
	 | arg {
     lista_arg.list=newListaParam();
     lista_arg.list.add(arg.tipo);
   }

arg: tipo_arg ID {
  if StackTSgetCima().getId(id.lexval) = -1{
    symbol *sym=crearSymbol(ID.val,tipo,dir,"var"); 
    insertar(getCimaSym(StackTS), sym);
    dir=dir+StackTT.getCima().getTam(tipo);
  }
  else
    Error("El identificador ya fue declarado");
  arg.tipo=tipo_arg.tipo;
}
;

tipo_arg: base param_arr {
  base=base.tipo
  tipo_arg.tipo=param_arr.tipo
}
;

param_arr: LCOR RCOR param_arr {
  param_arr

}
	 | /*vacia*/{}
;

sentencias: sentencias NL sentencia {}
	  | sentencia {}
;

sentencia: SI expresion_booleana ENTONCES NL sentencias NL FIN {}
	 | SI expresion_booleana NL sentencias NL SINO NL sentencias NL FIN {}
	 | MIENTRAS NL expresion_booleana HACER NL sentencias NL FIN {}
	 | HACER NL sentencia NL MIENTRASQUE NL expresion_booleana {}
	 | ID ASIGNA expresion {}
	 | ESCRIBIR expresion {}
	 | LEER variable {}
	 | DEVOLVER {}
	 | DEVOLVER expresion {}
	 | TERMINAR {}
;

expresion_booleana: expresion_booleana OO expresion_booleana {}
		  | expresion_booleana YY expresion_booleana {}
		  | NO expresion_booleana {}
		  | relacional {}
		  | VERDADERO {}
		  | FALSO {}

relacional: relacional GT relacional {}
	  | relacional LT relacional {}
    | relacional GE relacional {}
    | relacional LE relacional {}
    | relacional EQ relacional {}
    | relacional NE relacional {}
    | expresion {}
    ;


expresion: expresion MAS expresion {}
	 | expresion RES expresion {}
	 | expresion MUL expresion {}
	 | expresion DIV expresion {}
	 | expresion MOD expresion {}
	 | LPAR expresion RPAR {}
	 | variable {}
	 | NUM {}
	 | CADENA {}
	 | CARACTER {}
	 | ID LPAR parametros RPAR {}

variable: ID arreglo {}
	| ID PUNTO ID {}

arreglo: ID LCOR expresion RCOR arreglo {}
       | /*vacio*/

parametros: lista_param {}
	  | /*vacia*/

lista_param: lista_param COMA expresion {}
	   | expresion {}

%%

void yyerror(char *msg){
        printf("ERROR: %s en la linea %d\n\nEL PROGRAMA NO ES ACEPTADO\n", msg, yylineno-1);
        exit(-1);
}

extern FILE *yyin;
extern int yylex();
extern void yyerror(char *msg);
extern int yyparse();

int main(int argc, char **argv){
        FILE *f = fopen(argv[1], "r");
        if(argc <2) return -1;
        if(!f) return -1;
        yyin = f;
        yyparse();
        printf("\n EL PROGRAMA ES ACEPTADO\n");
        fclose(f);
        return 0;
}