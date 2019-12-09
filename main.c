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

/* ------ BIBLIOTECAS ------- */

%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tablaSimbolos.h"
#include "tablaTipos.h"
#include "estructuras.h"
#include "cuadrupla.h"

/* Funcion de errores sintácticos */
void yyerror(char* msg);

/* Variables recuperadas de lex*/
extern int yylex();
extern int yylineno;

/* Funciones para variables temporales, etiquetas e índices */
extern char *newLabel();
extern char *newIndex();
extern char *newTemp();
extern int backpatch(listTab* l, char* etiqueta, code * code);
extern int reducir (int dir, int tipo1, int tipo2);
extern int ampliar(int dir, int tipo1, int tipo2);
extern int max(int tipo1, int tipo2);

/* ------ Variables Globales ------ */
int tipoGbl; //Variable global que guarda el tipo de las pseudovariables
int dirGbl; //Variable global que guarda la dirección de las pseudovariables
int baseGbl; //Variable global que guarda la base de las pseudovariables

int funcTipo;// Variable que guarda el tipo de una función

typestack *stackTT; //Variable global de pila de tipos
symstack *stackTS; //Variable global de pila de símbolos
stackDir stackDirr = NULL; //Variable global de pila de direcciones

listTab *funcReturn; //Variable que guarda el tipo de retorno de una funcion

int contadorEtiqueta=0;
int contadorIndices=0;
int contadorTemp=0;
char *L, *L1;
char *I, *I1;
char *T, *T1;

code *codigoGbl; //¿Dónde se inicializa? Yo lo puse desde un principio
stringTab *stringT;
%}

/* ------- ESTRUCTURAS ------- */
%union{
  int dir;
  struct _num{
    int tipo;
    union {
      int eval;
      float rval;
      double dval;
      char cval;
    };
  }num;

  struct _lista{
    union{
      int ival; //para 
      char *cvar;
      int tipo;
      int dir;
    };
    struct _listTab *next;
    struct _listTab *verdadera;
    struct _listTab *falsa;
  }lista;

  struct{
    int tipo;
    int byte;
  } tipo;

  struct{
    char *sval;
    int dir;
    int tipo;
    char *base;
    int tam;
  }sval;

  struct{
    int cantidad;
  } cant;

  struct{
    struct _listParam *lista;
    int num;
    int list_argumentos[30][2];
  }argum;

  struct{
    int dir;
    int tipo;
    char* base;
  }exp;

  //Una union para registro
};

/* Terminales */
%token<sval> REGISTRO 
%token<sval> INICIO
%token<sval> FIN
%token<sval> TIPO 
%token<sval> BASE
%token<sval> ID
%token<sval> COMA
%token<sval> PUNTO
%token<sval> FUNC

%token<num> NUM 

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
%token<sval> OO
%token<sval> YY
%token<sval> NO
%token<sval> VERDADERO
%token<sval> FALSO
%token<sval> COMMENT
%token<sval> SPACE

%token<sval> CADENA
%token<sval> CARACTER
%token<sval> NL /*Salto de linea*/

/* Asociatividad y precedencia */
%right ASIGNA
%left OO
%left YY
%left EQ NE
%left GT LT GE LE
%left MAS RES
%left MOD
%left DIV MUL
%right NO
%nonassoc LPAR RPAR LCOR RCOR
%nonassoc SINO

/* Simbolos no terminales */
%type<sval> lista_var funciones variable arreglo parametros lista_param
%type<dec> declaraciones
%type<tipo> tipo tipo_registro base tipo_arreglo arg tipo_arg param_arr 
%type<argum> lista_arg argumentos
%type<lista> sentencias sentencia expresion_booleana relacional
%type<exp> expresion

/* Simbolo inicial */
%start programa

%%

programa: {
  dirGbl = 0; //Igualamos a 0 la variable global de dirección
  stackTT=crearTypeStack(); //Crear apuntador a pila de tipos
  stackTS=crearSymStack(); //Crear apuntador a pila de símbolos
  codigoGbl=crea_code(); //Creamos un apuntador a cuadrupla
  symtab *ts=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
  typetab *tt=crearTypeTab(); //Creamos una apuntador a una tabla de tipos
  insertarSymTab(ts,stackTS); //Insertamos en la pila la tabla de simbolos
  insertarTypeTab(tt,stackTT); //Insertamos en la pila la tabla de tipos
  stringT=crearTablaCadenas(); //Se crea el apuntador a la tabla de cadenas
}
declaraciones NL funciones 
;

declaraciones: /*vacia*/ {}
	     | tipo lista_var NL declaraciones {
         tipoGbl = $1.tipo;
         }
	     | tipo_registro lista_var NL declaraciones {
         tipoGbl = $1.tipo;
         }
         ;

tipo_registro: REGISTRO  NL INICIO declaraciones NL FIN {
          symtab *ts=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
          typetab *tt=crearTypeTab(); //Creamos una apuntador a una tabla de tipos
          pushDir(&stackDirr,dirGbl); //Insertamos en nuestra tabla de direcciones la dirección iniciada en 0
          dirGbl=0;  //Igualamos a 0 la variable global de dirección
          insertarTypeTab(tt,stackTT); //Insertamos en la pila la tabla de tipos
          insertarSymTab(ts,stackTS); //Insertamos en la pila la tabla de simbolos
          dirGbl = popDir(&stackDirr);
          typetab *tt1=crearTypeTab(); //Creamos una apuntador a una tabla de tipos temporal
          tt1 = sacarTypeTab(stackTT);
          //StackTS.getCima().setTT(tt1)//No se qué sea set, pienso que puede ser "insertar"
          symtab *ts1=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
          ts1 = sacarSymTab(stackTS);
          //dirGbl = popDir(&stackDirr);
          type *t=crearTipo();
          tipoGbl = $$.tipo;
          typetab *ttaux=getCimaType(stackTT);
          int n = ttaux->num; 
          llenarDatosTipo(ttaux,t,n+1,"registro",0,6,NULL,$$.tipo); //Segun yo es asi... 6 => registro
          insertarTipo(getCimaType(stackTT),t);
}
;

tipo: base tipo_arreglo {
           baseGbl=$1.tipo; //Guardamos en la variable global el tipo de base
           $$.tipo=$2.tipo; //Guardamos en la variable tipo el tipo del arreglo
}
;
base:  ENT{$$.tipo = 0;} //El 0 representa enteros
      |REAL{$$.tipo = 1;} //El 1 representa reales
      |DREAL{$$.tipo = 2;} //El 2 representa reales dobles
      |CAR{$$.tipo = 3;} //El 3 representa caracteres
      |SIN{$$.tipo = 4;} //El 4 representa sin tipo
;
tipo_arreglo: LCOR NUM RCOR tipo_arreglo {
    if($2.tipo = 0 && $2.eval > 0){
      //Creamos una variable tipo type      
      type *t = crearTipo();
      //Obtenemos la cima y la guardamos en una var temp
      typetab *ttaux = getCimaType(stackTT);
      /*Llenamos sus correspondientes datos*/
      //Variable que nos servira para asignar el id del tipo correspondiente
      int n = ttaux->num; 
      llenarDatosTipo(ttaux,t,n+1,"array",-1,$2.eval,NULL,$4.tipo);
      /*Insertamos el tipo y asignamos un valor al tipo de 
      tipo_arreglo, el cual sera el valor entero que 
      regrese la función insertarTipo()*/
      $$.tipo=insertarTipo(ttaux,t); 
    }
    else{
      yyerror("El indice tiene que ser entero y mayor que cero");
    }
  }
  | /*vacia*/ {
    $$.tipo = baseGbl;
  }
;

lista_var: lista_var COMA ID {
  if(buscar(getCimaSym(stackTS),$3.sval)==-1){
    symbol *s=crearSymbol($3.sval, tipoGbl, dirGbl, 0);
    insertar(getCimaSym(stackTS),s);
    dirGbl += getTam(getCimaType(stackTT),tipoGbl);
  }
  else
    yyerror("El identificador ya fue declarado");
}
	| ID { 
  if(buscar(getCimaSym(stackTS),$1.sval)==-1){
    symbol *s=crearSymbol($1.sval, tipoGbl, dirGbl, 0);
    insertar(getCimaSym(stackTS),s);
    dirGbl += getTam(getCimaType(stackTT),tipoGbl);
  }
  else
    yyerror("El identificador ya fue declarado");
  }
;

funciones: FUNC tipo ID LPAR argumentos RPAR INICIO NL declaraciones sentencias NL FIN NL funciones {
  if(buscar(stackTS->root,$3.sval)!=-1){//stackTS->root Sería igual a getFondo
    symbol *s=crearSymbol($3.sval, tipoGbl, -1, 1); //Modificar funcion
    insertar(stackTS->root,s);
    pushDir(&stackDirr,dirGbl);
    funcTipo = $2.tipo;
    funcReturn = crearTablaListas();
    dirGbl = 0;
    symtab *ts=crearSymTab(); //Creamos una apuntador a una tabla de simbolos
    typetab *tt=crearTypeTab(); //Creamos una apuntador a una tabla de tipos
    insertarTypeTab(tt,stackTT);
    insertarSymTab(ts,stackTS);
    agrega_cuadrupla(codigoGbl,"label","-","-",$3.sval);
    strcpy(L, newLabel());
    backpatch($10.next,L,codigoGbl);
    agrega_cuadrupla(codigoGbl,"label","-","-",L);
    sacarTypeTab(stackTT);
    sacarSymTab(stackTS);
    dirGbl = popDir(&stackDirr);
    ts=getCimaSym(stackTS);
    ts->root->params=$5.lista; //No estoy 100% segura
    if($2.tipo != 4 && funcReturn->root == NULL);
      yyerror("La funcion no tiene valor de retorno");
  }
  else
    yyerror("El identificador ya fue declarado");
}
	 | /*vacia*/{}
;

argumentos: lista_arg{
          //Segun yo lo que tenemos que hacer es nada más igualar las listas
          $$.lista=$1lista;
          //$$.num = $1.num; //Copia la cantidad de numero de argumentos
          //Esto no es necesario porque las estructuras son iguales
          /*for(int i=0;i<$1.num;i++){ //Copia los argumentos
              $$.list_argumentos[i][0] = $1.list_argumentos[i][0];
              $$.list_argumentos[i][1] = $1.list_argumentos[i][1];
          }*/
        }
	  | SIN{
        $$.list=NULL; // Segun yo es así
        //$$.num = 0;
      }
;

lista_arg: lista_arg arg {
        $$.list=$1.list;
        add($$.list,$2.tipo);
        $$.num = $1.num; 
        /*  for(int i=0;i<$1.num;i++){ //Copia los argumentos
              $$.list_argumentos[i][0] = $1.list_argumentos[i][0]; //tipo
              $$.list_argumentos[i][1] = $1.list_argumentos[i][1]; //id
          }
          Esto no va aquí como lo entiendo*/
}
	 | arg { 
     $$.list=crearLP();
     add($$.list,$1.tipo);
   }
   ;

arg: tipo_arg ID {
    if(buscar(getCimaSym(stackTS),$2.sval)==-1){
            symbol *s=crearSymbol($2.sval, tipoGbl, dirGbl, 0);
            insertar(getCimaSym(stackTS),s);
            dirGbl += getTam(getCimaType(stackTT),tipoGbl);
          }
    else
      yyerror("El identificador ya fue declarado\n");
    $$.tipo = $1.tipo;
}
;

tipo_arg: base param_arr {
  baseGbl = $1.tipo;
  $$.tipo = $2.tipo;
}
;

param_arr: LCOR RCOR param_arr {
  //Creamos una variable type
  type *t = crearTipo();
  //Obtenemos la cima y la guardamos en una var temp
  typetab *ttaux = getCimaType(stackTT);
  /*Llenamos sus correspondientes datos*/
  //Variable que nos servira para asignar el id del tipo correspondiente
  int n = ttaux->num; 
  llenarDatosTipo(ttaux,t,n+1,"array",-1,0,NULL,$3.tipo);
  /*Insertamos el tipo y asignamos un valor al tipo de
  param_arr, el cual será el valor entero que regrese
  la funcion insertarTipo()*/
  $$.tipo=insertarTipo(ttaux,t);
}
	 | /*vacia*/{
          $$.tipo = baseGbl;
   }
   ;

sentencias: sentencias NL sentencia {
    L=newLabel();
    backpatch($$.next,L,codigoGbl);
    $$.next=$1.next; //ESTO SI ES CORRECTO?
}
	  | sentencia {
      $$.next=$1.next; //ESTO SI ES CORRECTO?
    }
;

sentencia: SI expresion_booleana ENTONCES NL sentencias NL FIN {
      L=newLabel();
      backpatch($2,L,codigoGbl);
      $$.next=combinar($2.falsa,$5.next);
}
	 | SI expresion_booleana NL sentencias NL %prec SINO NL sentencias NL FIN {
       L=newLabel();
       L1=newLabel();
       backpatch($2.verdadera,L,codigoGbl);
       backpatch($2.falsa,L1,codigoGbl);
       $$.next=combinarListas($4.next,$8.next); 
   }
	 | MIENTRAS NL expresion_booleana HACER NL sentencias NL FIN {
       L=newLabel();
       L1=newLabel();
       backpatch($6.next,L,codigoGbl);
       backpatch($3.verdadera,L1,codigoGbl);
       $$.next=$3.falsa;
       agrega_cuadrupla(codigoGbl,"goto","-","-",L); 
   }
	 | HACER NL sentencia NL MIENTRASQUE NL expresion_booleana { //Revisar la gramática
       L=newLabel();
       L1=newLabel();
       backpatch($6.verdadera,L,codigoGbl);
       backpatch($3.next,L1,codigoGbl);
       $$.next=$6.falsa;
       agrega_cuadrupla(codigoGbl,"goto","-","-",L); 
   }
	 | ID ASIGNA expresion {
       symtab *staux=getCimaSym(stackTS);
         if(buscar(staux,$1.sval)!=-1){
           int t=getTipo(staux,$1.sval);
           int d=getDir(staux,$1.sval);
           char *temporal;
           char cadena[3];
           int a=reducir($3.dir,$3.tipo,t);
           sprintf(cadena,"%d",a);
           sprintf(temporal,"%s+%d",$1.sval,d); //Esto me hace más sentido
           agrega_cuadrupla(codigoGbl,"=",cadena,"-",temporal);
         }else{
           yyerror("El identificador no ha sido declarado");
         }
         $$.next=NULL;
   }
   | variable ASIGNA expresion{
     //a=reducir();
     agrega_cuadrupla(codigoGbl,"=",a,"-",d);
     $$.next=NULL;
   }
	 | ESCRIBIR expresion {
         //Creamos una variable code
         code *c=crea_code();
         /*Definimos una cadena auxiliar en donde guardaremos 
         el valor de dirGBL como cadena*/
         char cadena[3];
         //Convertimos el valor de dirGBL de entero a cadena
         sprintf(cadena,"%d",dirGbl);
         //Agregamos la cuadrupla
         agrega_cuadrupla(c,"print",cadena,"-","-");
         $$.next= NULL;
   }
	 | LEER variable {
         //Creamos una variable code
         code *c=crea_code();
         /*Definimos una cadena auxiliar en donde guardaremos 
         el valor de dirGBL como cadena*/
         char cadena[3];
         //Convertimos el valor de dirGBL de entero a cadena
         sprintf(cadena,"%d",dirGbl);
         //Agregamos la cuadrupla
         agrega_cuadrupla(c,"scan","-","-",cadena);
         $$.next= NULL;
   }
	 | DEVOLVER {
     if(funcTipo==4){
       agrega_cuadrupla(codigoGbl,"return","-","-","-");
     }else{
       yyerror("La funcion debe retornar algun tipo de valor %d",funcTipo);
     }
     $$.next= NULL;
   }
	 | DEVOLVER expresion {
         if(funcTipo!=4){
           int a=reducir($2.dir,$2.tipo,funcTipo);
           char cadena[3];
           //Convertimos el valor de dirGBL de entero a cadena
           sprintf(cadena,"%d",$2.dir);
           agrega_cuadrupla(codigoGbl,"return",cadena,"-","-");
           funcReturn=crearTablaListas();
         }else{
           yyerror("La funcion no puede retornar algun valor de tipo");
         }
         $$.next= NULL;
   }
	 | TERMINAR {
         I=newIndex();
         agrega_cuadrupla(codigoGbl,"goto","-","-",I);
         $$.next=crearTablaListas();
         agregaLista($$.verdadera,-1,I);
   }
;

expresion_booleana: expresion_booleana OO expresion_booleana {
        char *L=newLabel();
        backpatch();
        $$.verdadera=combinar($1.verdadera,$3.verdadera);
        $$.falsa=$3.falsa;
        agrega_cuadrupla(codigoGbl,"label","-","-",L);
}
		  | expresion_booleana YY expresion_booleana {
        char *L=newLabel();
        backpatch();
        $$.verdadera=$3.verdadera;
        $$.falsa=combinar($1.falsa,$3.falsa);
        agrega_cuadrupla(codigoGbl,"label","-","-",L);
      }
		  | NO expresion_booleana {
        $$.verdadera=$2.falsa;
        $$.falsa=$2.verdadera;
      }
		  | relacional {
        $$.verdadera=$1.verdadera;
        $$.falsa=$1.falsa;
      }
		  | VERDADERO {
        I=newIndex();
        $$.verdadera=crearTablaListas();
        agregaLista($$.verdadera,-1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I);
        $$.falsa=NULL;
      }
		  | FALSO {
        I=newIndex();
        $$.verdadera=NULL;
        $$.falsa=crearTablaListas();
        agregaLista($$.falsa,-1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I);
      }
;

relacional: relacional GT relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,">",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1);
}
	  | relacional LT relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,"<",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1);   
    }
    | relacional GE relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,">=",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1);  
    }
    | relacional LE relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,"<=",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1);  
    }
    | relacional EQ relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,"==",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1); 
    }
    | relacional NE relacional {
        $$.verdadera =  crearTablaListas();
        $$.falsa = crearTablaListas();
        I=newIndex();
        I1=newIndex();
        agregaLista($$.verdadera,-1,I); //el segundo argumento es un tipo que no deberia (int -> char)
        agregaLista($$.falsa,-1,I1); 
        $$.tipo=max($1.tipo,$3.tipo);
        int a1 = ampliar($1.dir,$1.tipo,$$.tipo);
        int a2 = ampliar($3.dir,$3.tipo,$$.tipo);
        char cadena[3];
        char cadena1[3];
        sprintf(cadena, "%d",a1);
        sprintf(cadena1, "%d",a2);
        agrega_cuadrupla(codigoGbl,"<>",cadena,cadena1,I);
        agrega_cuadrupla(codigoGbl,"goto","-","-",I1); 
    }
    | expresion {
      //relacional.tipo = expresion.tipo
      $$.tipo=$1.tipo;
      //relacional.dir = expresion.dir
      /*Tengo duda aqui, ¿relacional tiene un atrib 
      dir?*/
      $$.dir=$1.dir;
    }
    ;

expresion: expresion MAS expresion {
        //Obtenemos el tipo más grande de las expresiones
        $$.tipo=max($1.tipo,$3.tipo);

        $$.dir=8;
        /*Cadenas auxiliares para almacenar la conversión de
        entero a cadenas*/
        char c1[3], c2[3];
        int a1=ampliar($1.dir,$1.tipo,$$.tipo);
        int a2=ampliar($3.dir,$3.tipo,$$.tipo);
        /*Conversiones de entero a cadena para los argumentos
        de agrega_cuadrupla*/
        sprintf(c1,"%d",a1);
        sprintf(c2,"%d",a2);
        //agregamos la cuadrupla con el código correspondiente
        agrega_cuadrupla(codigoGbl,"+",c1,c2,newTemp());
}
	 | expresion RES expresion {
        //Obtenemos el tipo más grande de las expresiones
        $$.tipo=max($1.tipo,$3.tipo);

        $$.dir=8;
        /*Cadenas auxiliares para almacenar la conversión de
        entero a cadenas*/
        char c1[3], c2[3];
        int a1=ampliar($1.dir,$1.tipo,$$.tipo);
        int a2=ampliar($3.dir,$3.tipo,$$.tipo);
        /*Conversiones de entero a cadena para los argumentos
        de agrega_cuadrupla*/
        sprintf(c1,"%d",a1);
        sprintf(c2,"%d",a2);
        //agregamos la cuadrupla con el código correspondiente
        agrega_cuadrupla(codigoGbl,"-",c1,c2,newTemp());
   }
	 | expresion MUL expresion {
        //Obtenemos el tipo más grande de las expresiones
        $$.tipo=max($1.tipo,$3.tipo);

        $$.dir=8;
        /*Cadenas auxiliares para almacenar la conversión de
        entero a cadenas*/
        char c1[3], c2[3];
        int a1=ampliar($1.dir,$1.tipo,$$.tipo);
        int a2=ampliar($3.dir,$3.tipo,$$.tipo);
        /*Conversiones de entero a cadena para los argumentos
        de agrega_cuadrupla*/
        sprintf(c1,"%d",a1);
        sprintf(c2,"%d",a2);
        //agregamos la cuadrupla con el código correspondiente
        agrega_cuadrupla(codigoGbl,"*",c1,c2,newTemp());
   }
	 | expresion DIV expresion {
        //Obtenemos el tipo más grande de las expresiones
        $$.tipo=max($1.tipo,$3.tipo);

        $$.dir=8;
        /*Cadenas auxiliares para almacenar la conversión de
        entero a cadenas*/
        char c1[3], c2[3];
        int a1=ampliar($1.dir,$1.tipo,$$.tipo);
        int a2=ampliar($3.dir,$3.tipo,$$.tipo);
        /*Conversiones de entero a cadena para los argumentos
        de agrega_cuadrupla*/
        sprintf(c1,"%d",a1);
        sprintf(c2,"%d",a2);
        //agregamos la cuadrupla con el código correspondiente
        agrega_cuadrupla(codigoGbl,"/",c1,c2,newTemp());
   }
	 | expresion MOD expresion {
        //Obtenemos el tipo más grande de las expresiones
        $$.tipo=max($1.tipo,$3.tipo);

        $$.dir=8;
        /*Cadenas auxiliares para almacenar la conversión de
        entero a cadenas*/
        char c1[3], c2[3];
        int a1=ampliar($1.dir,$1.tipo,$$.tipo);
        int a2=ampliar($3.dir,$3.tipo,$$.tipo);
        /*Conversiones de entero a cadena para los argumentos
        de agrega_cuadrupla*/
        sprintf(c1,"%d",a1);
        sprintf(c2,"%d",a2);
        //agregamos la cuadrupla con el código correspondiente
        agrega_cuadrupla(codigoGbl,"%",c1,c2,newTemp());
   }
	 | LPAR expresion RPAR {
     $$.dir=$2.dir;
     //Asignamos valor al tipo del encabezado
     $$.tipo=$2.tipo;
   }
	 | variable {
        $$.dir=8;
        $$.tipo=$1.tipo;
        char cadena[3];
        sprintf(cadena, "%d",$1.dir);
        agrega_cuadrupla(codigoGbl,"*",cadena,"-",newTemp()); 
   }
	 | NUM {
     $$.tipo=$1.tipo;
     $$.dir=$1.cval;
   }
	 | CADENA {
       /*Se realiza esta acción semantica
       expresoin.tipo = num.tipo*/
       $$.tipo=$1.tipo;
       /*expresion.dir = TablaDeCadenas.add(cadena)*/
       /*Tengo duda aqui, la regla dice que se a expresion.dir
       se le debe asignar algo que regrese agregaCadena*/
       agregaCadena(stringT,$1.sval);
       $$.dir=strlen($1.sval);
   }
	 | CARACTER {
     $$.tipo = $1;
    /*expresion.dir = TablaDeCadenas.add(cadena)*/
    char *chain=creaCadena($1.sval);
    /*La misma duda que en lo anterior*/
    $$.dir=agregaCadena(stringT,chain); 
    $$.dir=strlen(chain);
   }
	 | ID LPAR parametros RPAR {
/*if(buscar(stackTS->root,$1.sval)!=-1){
         if(getTipoVar(stackTS->root,"func")!=-1){
           listParam *lista=getListParam(stackTS->root,$1.sval);
           
           if(getNumListParam(lista)!=$3.num)
             yyerror("El numero de elementos no coincide");
           
           int p2=$3.lista.root;
           param *p1=lista->root;
           /*No estoy seguro si esta parte este del todo bien
           for(int i=0;i<$3.num;i++){
             if(p1->tipo!=p2.ival){
               yyerror("El tipo de los parametros no coincide");
             }
             p1=p1->next;
             p2=$3.lista.next; //creo que todo lo demás está bien Fer 
           }//vale vale
           /*Esto creo que si
           $$.dir=newTemp();
           $$.tipo=getTipo(stackTS->root,$1.sval);
           agregar_cuadrupla(codigoGbl,"=","call",$1.sval,$$.dir);
         }
        }else{
         yyerror("El identificador no ha sido declarado");
       }*/
   }
   ;

variable: ID arreglo {
  $$.dir=$2.dir;
  $$.base=$2.base;
  $$.tipo=$2.tipo;
}
	| ID PUNTO ID {
        if (buscar(stackTS->root,$1.sval)!=-1){
          int t=getTipo(stackTS->root,$1.sval);
          if (t==6){
            int tipoBase=(getTipoBase(stackTT->root,t))->t->type;
            if (buscar(stackTS->root,$2.sval)!=-1){ //Tengo duda aquí amigos
              $$.tipo=tipoBase;
              $$.dir=$3.dir;
              char cadena[3];
              sprintf(cadena,"%d",$1.dir);
              $$.base=cadena;
            }
            else
              yyerror("El id no existe en la estructura");
          }
          else
            yyerror("El id no es una estructura");
        }
        else
          yyerror("El id no ha sido declarado");clarado");
  }
;
arreglo: ID LCOR expresion RCOR {
        if (buscar(stackTS->root,$1.sval)!=-1){
          int t=getTipo(stackTS->root,$1.sval);
          if (t==7){
            if ($3.tipo==0){ 
              $$.base=$1.sval;
              $$.tipo=(getTipoBase(getCimaType(stackTT),t))->t->type;
              $$.tam=getTam(getCimaType(stackTT),$$.tipo);
              T = newTemp();
              $$.dir=strlen(T);
              char cadena[3],cadena1[3],cadena2[3];
              sprintf(cadena,"%d", $3.dir);
              sprintf(cadena1,"%d", $$.tam);
              sprintf(cadena2,"%d", $$.dir);
              agrega_cuadrupla(codigoGbl,"*",cadena,cadena1,cadena2);
            }
            else
              yyerror("La expresion para un indice debe ser de tipo entero");
          }
          else
            yyerror("El id no es un arreglo");
        }
        else
          yyerror("El id no ha sido declarado");
  }
  | arreglo LCOR expresion RCOR {
      if (buscar(stackTS->root,$1.sval)!=-1){
          int t=getTipo(stackTS->root,$1.sval);
          if (t==7){
            $$.base=$1.base;
            $$.tipo=(getTipoBase(getCimaType(stackTT),t))->t->type;
              $$.tam=getTam(getCimaType(stackTT),$$.tipo);
            T=newTemp();
            T1=newTemp();
            $$.dir=strlen(T1);
            char cadena[3],cadena1[3];
            sprintf(cadena,"%d", $3.dir);
            sprintf(cadena1,"%d", $$.tam);
            agrega_cuadrupla(codigoGbl,"*",cadena,cadena1,T);
            sprintf(cadena,"%d", $1.dir);
            sprintf(cadena1,"%d", $$.dir);
            agrega_cuadrupla(codigoGbl,"+",cadena,T,cadena1);
          }
          else
            yyerror("La expresion para un indice debe ser de tipo entero");
        }
        else
          yyerror("El arreglo no tiene tantas dimensiones");
  }
;

parametros: lista_param { $$.lista=$1.lista; }
	  | /*vacia*/{$$.lista=NULL;}
;

lista_param: lista_param COMA expresion {
  $$.lista=$1.lista
  add($$.lista,$1.tipo);
  agrega_cuadrupla(codigoGbl,"param",$3.dir,"-","-");
}
	   | expresion {
       $$.lista=creaLP();
       add($$.lista,$1.tipo);
       agrega_cuadrupla(codigoGbl,"param",$1.dir,"-","-");
     }
;
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

char *newLabel(){
        char *label = (char *)malloc(45*sizeof(char));
        contadorEtiqueta++;
        sprintf(label, "L%d", contadorEtiqueta);
        return label;
}

//Función para crear nuevos índices
char *newIndex(){
        char *index = (char *)malloc(45*sizeof(char));
        contadorIndices++;
        sprintf(index, "I%d", contadorIndices);
        return index;
}

//Función para crear temporales
char *newTemp(){        
        char *temp = (char *)malloc(45*sizeof(char));
        contadorTemp++;
        sprintf(temp, "T%d", contadorTemp);
        return temp;
}


int backpatch(listTab* l, char* etiqueta, code * code){
  quad *tempc = code->root;
  list *templ = l->root;
    for(int i=0; i < l->num_listas; i++){
        for(int j=0; j < code->num_instrucciones; j++){
            if(strcmp(tempc->res, templ->str)==0){
                strcpy(tempc->res, etiqueta);
            }
        }
    }
}

int reducir(int dir, int tipo1, int tipo2){
    char *temp=(char*)malloc(45*sizeof(char));
    char caux[3];
    int n;
     if(tipo1==tipo2)
         return dir;
    //Reduciendo de real a ent
     else if(tipo1==0 && tipo2==1){
         temp=newTemp();
         sprintf(caux,"t%d",dir);
         agrega_cuadrupla(codigoGbl,"=","(ent)",caux,temp);
         listarCode(codigoGbl);
         n=contadorTemp;
         return n;
     }
     //Reduciendo de dreal a ent
     else if(tipo1==0 && tipo2==2){
         temp=newTemp();
         sprintf(caux,"t%d",dir);
         agrega_cuadrupla(codigoGbl,"=","(ent)",caux,temp);
         listarCode(codigoGbl);
         n=contadorTemp;
         return n;
     }
     //Reduciendo de dreal a real
     else if(tipo1==1 && tipo2==2){
         temp=newTemp();
         sprintf(caux,"t%d",dir);
         agrega_cuadrupla(codigoGbl,"=","(real)",caux,temp);
         listarCode(codigoGbl);
         n=contadorTemp;
         return n;
     }
     //Caso por default
     printf("ERROR:no se puede reducir del tipo %d al tipo %d\n",tipo1,tipo2);
     return -1;
}



//Función para ampliar un tipo de dato
int ampliar(int dir, int tipo1, int tipo2){
	char *temp=(char*)malloc(45*sizeof(char));
	char caux[3];
	int n;
    if(tipo1==tipo2)
        return dir;
    //Comparamos ent y car
    else if((tipo1==0 && tipo2==3) || (tipo1==3 && tipo2==0)){
        temp = newTemp();
        sprintf(caux,"t%d",dir);
        agrega_cuadrupla(codeGBL,"=","(ent)",caux,temp);
        listarCode(codeGBL);
        n=contadorTemp;
        return n;
    }
    //Comparamos ent y real    
    else if((tipo1==0 && tipo2==1) || (tipo1==1 && tipo2==0)){
        temp = newTemp();
        sprintf(caux,"t%d",dir);
        agrega_cuadrupla(codeGBL,"=","(real)",caux,temp);
        listarCode(codeGBL);
        n=contadorTemp;
        return n;
    }
    //Comparamos ent y dreal    
    else if((tipo1==0 && tipo2==2) || (tipo1==2 && tipo2==0)){
        temp = newTemp();
        sprintf(caux,"t%d",dir);
        agrega_cuadrupla(codeGBL,"=","(dreal)",caux,temp);
        listarCode(codeGBL);
        n=contadorTemp;
        return n;
    }
    //Comparamos real y dreal    
    else if((tipo1==1 && tipo2==2) || (tipo1==2 && tipo2==1)){
        temp = newTemp();
        sprintf(caux,"t%d",dir);
        agrega_cuadrupla(codeGBL,"=","(dreal)",caux,temp);
        listarCode(codeGBL);
        n=contadorTemp;
        return n;
    }
    else
        yyerror("No se pudo ampliar el tipo de dato");
}

//Función para maximizar los tipos de datos
int max(int tipo1, int tipo2){
    if(tipo1 == tipo2)
        return tipo1;
    //Comparamos ent y car
    else if((tipo1==0 && tipo2==3) || (tipo1==3 && tipo2==0)){
        return 0;
    }
    //Comparamos ent y real    
    else if((tipo1==0 && tipo2==1) || (tipo1==1 && tipo2==0)){
        return 1;
    }
    //Comparamos ent y dreal    
    else if((tipo1==0 && tipo2==2) || (tipo1==2 && tipo2==0)){
        return 2;
    }
    //Comparamos real y dreal    
    else if((tipo1==1 && tipo2==2) || (tipo1==2 && tipo2==1)){
        return 2;
    }
    else
        yyerror("No se pudo maximizar el tipo de dato");
}



