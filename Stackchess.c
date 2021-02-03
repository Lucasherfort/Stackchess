#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>


/* LISTES DES FONCTIONS */

void Initialisation();
void Game();
void Deplacement();
void Rafraichir();
void Test();
void MovePiece();
void MovePion();
void MoveTour();
void MoveFou();
void MoveDameEtRoi();
void MoveCavalier();
void PopAndPush();


/* STRUCTURE DES PILES */

#define N 100
struct stack{char* content[N]; int summit;};

typedef struct stack stack;


/*
@ requires : Rien.
@ assigns : Le sommet de la pile r prend la valeur -1.
@ ensures : Retourne une pile vide.
*/
stack create()
{
  stack r;
  r.summit = -1;
  return r;
}

/*
@ requires : Une pile s.
@ assigns : Rien. 
@ ensures : Retourne 1 si la pile s est vide, 0 sinon.
*/
int is_empty(stack s)
{
  if(s.summit < 0)
    return 1;
  return 0;
}

/*
@ requires : Une pile s et un char* i.
@ assigns : Ajoute i au sommet de la pile s. 
@ ensures : Rien.
*/
void push(char* i, stack *s)
{
  s->summit = s->summit + 1;
  s->content[s->summit] = i;
}

/*
@ requires : Un pointeur s vers une pile
@ assigns : Sommet de la pile. 
@ ensures : l'élément supprimé .
*/
char* pop(stack *s)
{
  char* r;
  r = s->content[s->summit];
  s->summit = s->summit - 1;
  return r;
}

/*
@ requires : Pile s.
@ assigns : e 
@ ensures : Retourne e.
*/
char* sommet(stack s)
{
  char* e;
  e = s.content[s.summit];
  return e;
}

/*
@ requires : Pile s.
@ assigns : Rien.
@ ensures : Taille de la pile s.
*/
int TaillePile(stack s)
{
  stack tmp;
  int i;
  
  i = 0;
  tmp = s;
  while(!is_empty(tmp))
    {
      pop(&tmp);
      i = i+1;
    }
  return i;
}

/* VARIABLES GLOBALES */


/* Permet de numéroter toutes les cases du plateau de jeu */
int Coordonnees[8][8] = {{1,2,3,4,5,6,7,8},
			 {9,10,11,12,13,14,15,16},
			 {17,18,19,20,21,22,23,24},
			 {25,26,27,28,29,30,31,32},
			 {33,34,35,36,37,38,39,40},
			 {41,42,43,44,45,46,47,48},
			 {49,50,51,52,53,54,55,56},
			 {57,58,59,60,61,62,63,64}};

/* Permet d'identifier les cases présentent sur le plateau de jeu */
char ChoixChiffre[8] = {'1','2','3','4','5','6','7','8'};
char ChoixLettre[8] = {'a','b','c','d','e','f','g','h'};

/* Stocke les cases de départ des pions blancs et noirs */
int CasePionBlancs[8] = {49,50,51,52,53,54,55,56};
int CasePionNoirs[8] = {9,10,11,12,13,14,15,16};


/* Stocke le nom des cases avec la lettre et le chiffre */
char* Echiquier[64] = {"a8","b8","c8","d8","e8","f8","g8","h8",
                       "a7","b7","c7","d7","e7","f7","g7","h7",
                       "a6","b6","c6","d6","e6","f6","g6","h6",
		       "a5","b5","c5","d5","e5","f5","g5","h5",
		       "a4","b4","c4","d4","e4","f4","g4","h4",
		       "a3","b3","c3","d3","e3","f3","g3","h3",
		       "a2","b2","c2","d2","e2","f2","g2","h2",
		       "a1","b1","c1","d1","e1","f1","g1","h1"};

/* Stocke le plateau de jeu pour ensuite l'affiché avec la fonction printf */
char *Piece[64] = {"TN","CN","FN","DN","RN","FN","CN","TN",
		   "PN","PN","PN","PN","PN","PN","PN","PN",
		   "  ","  ","  ","  ","  ","  ","  ","  ",
		   "  ","  ","  ","  ","  ","  ","  ","  ",
		   "  ","  ","  ","  ","  ","  ","  ","  ",
		   "  ","  ","  ","  ","  ","  ","  ","  ",
		   "PB","PB","PB","PB","PB","PB","PB","PB",
		   "TB","CB","FB","DB","RB","FB","CB","TB"};

/* Liste toutes les pièces blanches et noires */
char *PieceNoire[6] = {"PN","TN","FN","DN","RN","CN"};
char *PieceBlanche[6] = {"PB","TB","FB","DB","RB","CB"};

/* Garde en mémoire, la case de départ, la case d'arrivée, le nombre de pièce que 
le joueur souhaite déplacer sous forme de caractère */
char coup,cible,NombreDePiece;

/* Garde en mémoire, la case de départ, la case d'arrivée, le nombre de pièce que 
le joueur souhaite déplacer ainsi que le nombre de coup restant sous forme de int */
int depart,arrive,PieceDeplace,CoupRestant;

/* Premet aux joueurs de joueur chacun leur tour ; 1 = blanc et 0 = noirs */ 
int Joueur = 1;

/* Stocke le nombre de pièce noire et blanches restantent sur le plateau de jeu */ 
int PieceBrestantes = 16;
int PieceNrestantes = 16;

int k; /* pour savoir si le pion doit se transformer en dame */

/* Déclaration de toutes les piles correspondant à toutes les cases du plateau de jeu */ 
stack a1,a2,a3,a4,a5,a6,a7,a8,
  b1,b2,b3,b4,b5,b6,b7,b8,
  c1,c2,c3,c4,c5,c6,c7,c8,
  d1,d2,d3,d4,d5,d6,d7,d8,
  e1,e2,e3,e4,e5,e6,e7,e8,
  f1,f2,f3,f4,f5,f6,f7,f8,
  g1,g2,g3,g4,g5,g6,g7,g8,
  h1,h2,h3,h4,h5,h6,h7,h8,
  vide,currentPile,PileCible;

/* Tableau contenant les 64 piles ci dessus */ 
stack T[64];

/*
@ requires : Rien.
@ assigns : tableau T 
@ ensures : Rien.
*/
void Initialisation()
{
  /* Affigage du plateau de jeu à l'état initial */
  
  printf("   a  b  c  d  e  f  g  h \n");
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",8, Piece[0],Piece[1],Piece[2],Piece[3],Piece[4],Piece[5],Piece[6],Piece[7]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",7, Piece[8],Piece[9],Piece[10],Piece[11],Piece[12],Piece[13],Piece[14],Piece[15]);   
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",6, Piece[16],Piece[17],Piece[18],Piece[19],Piece[20],Piece[21],Piece[22],Piece[23]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",5, Piece[24],Piece[25],Piece[26],Piece[27],Piece[28],Piece[29],Piece[30],Piece[31]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",4, Piece[32],Piece[33],Piece[34],Piece[35],Piece[36],Piece[37],Piece[38],Piece[39]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",3, Piece[40],Piece[41],Piece[42],Piece[43],Piece[44],Piece[45],Piece[46],Piece[47]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",2, Piece[48],Piece[49],Piece[50],Piece[51],Piece[52],Piece[53],Piece[54],Piece[55]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s| \n",1, Piece[56],Piece[57],Piece[58],Piece[59],Piece[60],Piece[61],Piece[62],Piece[63]);
  printf(" +--+--+--+--+--+--+--+--+ \n");
  printf("\n");

  /* Création de toutes les piles du plateau de jeu */
  
  a1 = create();
  a2 = create();
  a3 = create();
  a4 = create();
  a5 = create();
  a6 = create();
  a7 = create();
  a8 = create();
  b1 = create();
  b2 = create();
  b3 = create();
  b4 = create();
  b5 = create();
  b6 = create();
  b7 = create();
  b8 = create();
  c1 = create();
  c2 = create();
  c3 = create();
  c4 = create();
  c5 = create();
  c6 = create();
  c7 = create();
  c8 = create();
  d1 = create();
  d2 = create();
  d3 = create();
  d4 = create();
  d5 = create();
  d6 = create();
  d7 = create();
  d8 = create();
  e1 = create();
  e2 = create();
  e3 = create();
  e4 = create();
  e5 = create();
  e6 = create();
  e7 = create();
  e8 = create();
  f1 = create();
  f2 = create();
  f3 = create();
  f4 = create();
  f5 = create();
  f6 = create();
  f7 = create();
  f8 = create();
  g1 = create();
  g2 = create();
  g3 = create();
  g4 = create();
  g5 = create();
  g6 = create();
  g7 = create();
  g8 = create();
  h1 = create();
  h2 = create();
  h3 = create();
  h4 = create();
  h5 = create();
  h6 = create();
  h7 = create();
  h8 = create();
  vide = create();
  currentPile = create();

  /* Empilage des piles à l'état initial */

  push("TB",&a1);
  push("CB",&b1);
  push("FB",&c1);
  push("DB",&d1);
  push("RB",&e1);
  push("FB",&f1);
  push("CB",&g1);
  push("TB",&h1);

  push("PB",&a2);
  push("PB",&b2);
  push("PB",&c2);
  push("PB",&d2);
  push("PB",&e2);
  push("PB",&f2);
  push("PB",&g2);
  push("PB",&h2);

  push("PN",&a7);
  push("PN",&b7);
  push("PN",&c7);
  push("PN",&d7);
  push("PN",&e7);
  push("PN",&f7);
  push("PN",&g7);
  push("PN",&h7);

  push("TN",&a8);
  push("CN",&b8);
  push("FN",&c8);
  push("DN",&d8);
  push("RN",&e8);
  push("FN",&f8);
  push("CN",&g8);
  push("TN",&h8);

  /* Ajout de toutes les piles du plateau de jeu dans le tableau T */

  T[0] = a8;
  T[1] = b8;
  T[2] = c8;
  T[3] = d8;
  T[4] = e8;
  T[5] = f8;
  T[6] = g8;
  T[7] = h8;
  T[8] = a7;
  T[9] = b7;
  T[10] = c7;
  T[11] = d7;
  T[12] = e7;
  T[13] = f7;
  T[14] = g7;
  T[15] = h7;
  T[16] = a6;
  T[17] = b6;
  T[18] = c6;
  T[19] = d6;
  T[20] = e6;
  T[21] = f6;
  T[22] = g6;
  T[23] = h6;
  T[24] = a5;
  T[25] = b5;
  T[26] = c5;
  T[27] = d5;
  T[28] = e5;
  T[29] = f5;
  T[30] = g5;
  T[31] = h5;
  T[32] = a4;
  T[33] = b4;
  T[34] = c4;
  T[35] = d4;
  T[36] = e4;
  T[37] = f4;
  T[38] = g4;
  T[39] = h4;
  T[40] = a3;
  T[41] = b3;
  T[42] = c3;
  T[43] = d3;
  T[44] = e3;
  T[45] = f3;
  T[46] = g3;
  T[47] = h3;
  T[48] = a2;
  T[49] = b2;
  T[50] = c2;
  T[51] = d2;
  T[52] = e2;
  T[53] = f2;
  T[54] = g2;
  T[55] = h2;
  T[56] = a1;
  T[57] = b1;
  T[58] = c1;
  T[59] = d1;
  T[60] = e1;
  T[61] = f1;
  T[62] = g1;
  T[63] = h1;

  Game();
}

/*
@ requires : Rien.
@ assigns : Stocke la case entrée par le joueur dans la variable coup. 
@ ensures : Deplacement si la partie n'est pas fini sinon exit(1).
*/
void Game()
{
  int i;
  
  /* S'i y a encore des pièces sur le plateau de jeu */
  if(PieceBrestantes != 0 && PieceNrestantes != 0)
    {
      /*C'est au tour des blancs de joueur */
      if (Joueur == 1)
	{
	  printf("C'est au tour des blancs. Quel est votre choix ? ");
	}

      /*C'est au tour des noirs de joueur */
      else
	{
	  printf("C'est au tour des noirs. Quel est votre choix ? ");
	}
      printf("\n");

      scanf("%s",&coup); /* récupère la case choisie par le joueur et elle est stockée dans coup */

      for(i = 0; i < 64; i=i+1) /* Pour chaque case du plateau de jeu */
	{
	  if(strcmp(&coup, Echiquier[i]) == 0) /* Si la case choisie se trouve sur le plateau de jeu */
	    {
	      printf("\n");
	      Deplacement(0); 
	    }
	}
      
      printf("\n");

      /* Si la case choisie ne se trouve sur le plateau de jeu */
      printf("La case %1s n'existe pas.\n",&coup);

      /* On relance la fonction Game afin de demander au joueur de selectionner une autre
      case de départ*/
      Game();
    }
  else if(PieceBrestantes == 0) /* S'il n'y a plus de piècse blanches sur le plateau de jeu */
    {
      printf("Les noirs ont gagnés la partie\n");
      exit(1); /* On stope le programme */
    }
  else if(PieceNrestantes == 0) /* S'il n'y a plus de pièces noires sur le plateau de jeu */
    {
      printf("Les blancs ont gagnés la partie\n");
      exit(1); /* On stope le programme */
    }
}

/*
@ requires : i >= 0.
@ assigns : Si i = 0, currentPile et départ sinon, PileCible et arrive.
@ ensures : Rien.
*/
void Deplacement(int i)
{
  int j = 0;
  if(i == 0) /* On cherche la pile de départ ainsi que le numéro de la case de départ */
    {
      /* La boucle se termine dès que qu'on repère la case de départ sur l'echiquier */
      while(strcmp(&coup,Echiquier[j]) != 0) /* Comparaison de coup avec les cases de l'echiquier */
	{
	  j=j+1;
	}
      /* A la fin de la boucle j correspond à la position de la case sur le plateau de jeu ce 
      qui permet de selectionner la pile de départ dans T car elles sont rangées dans le même ordre */

      currentPile = T[j]; /* Stocke la pile de départ dans currentPile */
      depart = j+1; /* Stocke le numéro de la case de départ dans depart */
      Rafraichir(currentPile,0); /* Lance la fonction Rafraichir () */
    }

  /* On cherche la pile d'arrivée ainsi que le numéro de la case d'arrivée */
  else
    {
      while(strcmp(&cible,Echiquier[j]) != 0)
	{
	  j=j+1;
	}
      PileCible = T[j];
      arrive = j+1;

      /* Test si les cases de départ et d'arrivée sont identiques */
      if(depart == arrive)
	{
	  printf("Votre case d'arrive ne peut pas etre identique à celle de départ\n");

	  /* On relance la fonction MovePiece afin de demander au joueur de choisir une autre case cible */
	  MovePiece();
	}
    }
}

/*
@ requires :Pile p et  aff >= 0.
@ assigns : AffichePile,lettre.
@ ensures : Rien.
*/
void Rafraichir(stack p, int aff)
{
  char lettre;
  stack copie,tmp1,tmp;
  copie = p;
  tmp1 = create();
  tmp = create();
  int i = 0;
  
  char* e;

  /* Tableau servant pour l'affichage de la pile de départ */
  char* AffichePile[16] = {"  ", "  ", "  ", "  ", "  ", "  ", "  ", "  ","  ", "  ", "  ", "  ", "  ", "  ", "  ", "  "};
  
  /* 16 pieces max à l'empilage */
  if(!is_empty(copie))
    {
      /* Desempilage de copie puis empilage de tmp1 */
      while(!is_empty(copie))
	{
	  e = sommet(copie);
	  push(e,&tmp1);
          pop(&copie);
        }
      /* Desempilage de tmp1 puis empilage de tmp */
      while(!is_empty(tmp1))
	{
	  e = sommet(tmp1);

	  /* Tant que tmp1 n'est pas vide, chaque case de AffichePile prennent la valeur des sommets de tmp1 */ 
	  AffichePile[i] = e;
	  push(e,&tmp);
          pop(&tmp1);
	  i = i+1;
        }
    }

  /* Si la pile copie n'est vide */
  else
    {
      tmp = copie;
    }

  /* Affichage du plateau de jeu avec les éléments de la pile de départ */
  
  printf("   a  b  c  d  e  f  g  h \n");
  printf(" +--+--+--+--+--+--+--+--+\n");
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",8, Piece[0],Piece[1],Piece[2],Piece[3],Piece[4],Piece[5],Piece[6],Piece[7],AffichePile[15]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[14]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",7, Piece[8],Piece[9],Piece[10],Piece[11],Piece[12],Piece[13],Piece[14],Piece[15],AffichePile[13]);   
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[12]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",6, Piece[16],Piece[17],Piece[18],Piece[19],Piece[20],Piece[21],Piece[22],Piece[23],AffichePile[11]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[10]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",5, Piece[24],Piece[25],Piece[26],Piece[27],Piece[28],Piece[29],Piece[30],Piece[31],AffichePile[9]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[8]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",4, Piece[32],Piece[33],Piece[34],Piece[35],Piece[36],Piece[37],Piece[38],Piece[39],AffichePile[7]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[6]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",3, Piece[40],Piece[41],Piece[42],Piece[43],Piece[44],Piece[45],Piece[46],Piece[47],AffichePile[5]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[4]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",2, Piece[48],Piece[49],Piece[50],Piece[51],Piece[52],Piece[53],Piece[54],Piece[55],AffichePile[3]);
  printf(" +--+--+--+--+--+--+--+--+      %1s\n",AffichePile[2]);
  printf("%d|%s|%s|%s|%s|%s|%s|%s|%s|      %1s\n",1, Piece[56],Piece[57],Piece[58],Piece[59],Piece[60],Piece[61],Piece[62],Piece[63],AffichePile[1]);

  /* Si la pile tmp n'est pas vide tu affiches le nom de la pile de départ */
  if(!is_empty(tmp))
    printf(" +--+--+--+--+--+--+--+--+  %s: %1s\n",&coup,AffichePile[0]);

  /* Sinon, tu n'affiches rien */
  else
    printf(" +--+--+--+--+--+--+--+--+ \n");

  /* aff = 0 => on va demander une lettre au joueur 
     aff != 0 =>  on va juste rafraichir l'affichage après un déplacement et changer de joueur */
  if(aff == 0 && CoupRestant == 0)
    {
      /* Verifie que la case choisie contient au moins une pièce */
      if(is_empty(tmp))
	{
	  printf("\n");
	  printf("La case choisie ne contient pas de piece \n");
	  Game();
	}

      printf("\n");
      printf("Que souhaitez vous faire ? veuilez entrer une lettre : \n");
      
      /* Demande au joueur de renter une lettre */
      scanf("%s", &lettre);

      /* Si la lettre est c alors on rafraichir l'affichage avec la pile vide et on demande
      au joueur de chosiir une nouvelle case de départ */
      if(lettre == 'c')
	{
	  Rafraichir(vide,1);
	  Game();
	}

      /* Si la lettre est d alors on vérifie que la pièce présente au sommet de current appartiennt bien
      au joueur en cours */
      else if(lettre == 'd')
	{
	  if(Joueur == 1 && strchr(sommet(currentPile), 'B') != NULL)

	    /* On lance Test quand c'est OK */
	    Test();
	  else if(Joueur == 0 && strchr(sommet(currentPile), 'N') != NULL)

	    /* On lance Test quand c'est OK */
	    Test();
	  
	  printf("Les pieces présentent ne vous appartient pas \n");
	  
	  /* On relance Rafraichir avec aff = 1 pour demander au joueur de choisir une nouvelle case de départ */
	  Rafraichir(vide,1);
	  
	}

      /* Si la lettre est a, le joueur en cours abandonne la partie */
      else if(lettre == 'a')
	{
	  if (Joueur == 1)
	    {
	      printf("Les noirs gagnent par forfait \n");
	    }
	  else
	    {
	      printf("Les blancs gagnent par forfait \n");
	    }
	  exit(1); /* Arrete le programme */
	}
      
      printf("La lettre %s n'est pas correct\n",&lettre);
      
      /* Si la lettre n'est pas correct, on demande au joueur de choisir une nouvelle case de départ */
      Rafraichir(vide,1);
    }

  /* On demande au joueur de choisir une nouvelle case de départ en appellant la fonction Game */
  else if(aff == 1)
    {
      printf("\n");
      Game();
    }


  /* Si le joueur a encore des pièces à déplacer, on appelle la fonction MovePiece  */
  else if(CoupRestant != 0)
    {
      printf("\n");
      MovePiece();
    }
  
}

/*
@ requires : Rien.
@ assigns : NombrePiece, PieceDeplace et CoupRestant.
@ ensures : Rien.
*/
void Test()
{
  char* e;
  int l;
  
  e = sommet(currentPile);
  l = TaillePile(currentPile);

  if(l != 1) /* currentPile contient plus de 2 pièces */
    {
      printf("Veuillez choisir un nombre de piece a deplacer :\n");
      scanf("%s",&NombreDePiece); /* nombre entré par le joueur */
      PieceDeplace = atoi(&NombreDePiece); /* Permet de vérifier que le joueur a bien saisi un entier */
    }
  else
    {
      PieceDeplace = 1;
    }


  if(PieceDeplace == 0)
    {
      printf("Nombre de piece incorrects :\n");
      Test();
    }

  if(PieceDeplace >= l+1)
    {
      printf("La case contient %i vous ne pouvez donc pas déplacer %i pièces\n",l, PieceDeplace);
      Test();
    }
  
  
  CoupRestant = PieceDeplace;
  
 /* Verifie que la pièce contenue sur la case de départ appartient au joueur */
  if((Joueur == 1 && strchr(e, 'B') != NULL) || (Joueur == 0 && strchr(e, 'N') != NULL))
     MovePiece();
}

/*
@ requires : Rien.
@ assigns : cible.
@ ensures : Rien.
*/
void MovePiece()
{
  int i;
  
  printf("Veuillez choisir une case cible pour %1s :\n",sommet(currentPile));
  scanf("%s",&cible); /* case cible rentrée par le joueur */
  
  for(i = 0; i < 64; i=i+1)
    {
      if(strcmp(&cible, Echiquier[i])== 0) /* vérifie que la case cible se trouve bien sur le plateau de jeu */
	{
	  Deplacement(1); /* On récupère la pile cible ainsi que son numéro */
	  if(strchr(sommet(currentPile), 'P') != NULL) 
	    {
	      MovePion(); /* On lance MovePion() si la pièce présente au sommet de la pile cible est un pion */
	    }
	  else if(strchr(sommet(currentPile), 'T') != NULL)
	    {
	      MoveTour(); /* On lance MoveTour() si la pièce présente au sommet de la pile cible est une tour */
	    }
	  else if(strchr(sommet(currentPile), 'F') != NULL)
	    {
	      MoveFou(); /* On lance MoveFou() si la pièce présente au sommet de la pile cible est un fou */
	    }

	  else if(strchr(sommet(currentPile), 'C') != NULL)
	    {
	      MoveCavalier(); /* On lance MoveCavalier() si la pièce présente au sommet de la pile cible est un cavalier */
	    }

	  else if(strchr(sommet(currentPile), 'D') != NULL || strchr(sommet(currentPile), 'R') != NULL)
	    {
	      MoveDameEtRoi(); /* On lance MoveDameEtRoi() si la pièce présente au sommet de la pile cible est une dame ou un roi */
	    }
	}
    }

  /* Si on arrive ici c'est que la case cible que le joueur souhaite n'éxiste pas */
  printf("La case %1s n'existe pas \n",&cible);
  MovePiece();
}

/*
@ requires : Rien.
@ assigns : ld,la,Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/
void MovePion()
{
  int i;

  int j,k;
  int ld,la;

  /* Détermine la ligne de départ et d'arrivée pour corrigé le bug évoqué dans mon rapport */
   for(j = 0 ; j < 8 ; j = j+1)
     {
     for(k = 0 ; k < 8 ; k = k+1)
       {
	 if(Coordonnees[j][k] == depart)
	   {
	     ld = j+1;
	   }
	 if(Coordonnees[j][k] == arrive)
	   {
	     la = j+1;
	   }
       }
     }
  /* Les blancs jouent actuellement */
  if(Joueur == 1)
    {
      /* vérifie que le joueur veut déplacer un pion d'une case ou de deux cases */
      if(fabs(arrive - depart) == 8 || fabs(arrive - depart) == 16)
	{
	  /* déplacement d'une case */
	  if(fabs(arrive - depart) == 8 && arrive < depart)
	    {
	      /* vérifie que la case cible est vide ou contient une pièce blanche */
	      if((strcmp(Piece[arrive - 1], "  ") == 0 || strchr(sommet(PileCible), 'B') != NULL))
		{

		  /* Déplacement du pion sur le plateau de jeu */
		  Piece[depart - 1] = "  ";
		  k=0;

		  /* test si le pion peut se transformer en dame */
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[0][i] == arrive)
			k = 1;
		    }

		  if(k == 0) /* Si le pion peut se transformer en dame alors on affiche une dame blanche */
		    Piece[arrive - 1] = "PB";
		  else /* sinon on affiche un pion blanc */
		    Piece[arrive - 1] = "DB";

		  
		  PopAndPush(0); /* on désempile la pile de départ */
	          PopAndPush(1); /* on empile la pile d'arrivée */
		  CoupRestant =  CoupRestant - 1; 
		  
		  /* Si le joueur a encore des pièces à déplacer */
		  if(CoupRestant != 0)
		    Deplacement(0); /* MAJ de l'affichage avec la pile de départ actualisée */
		  
                  /* C'est au tour des noirs de jouer */
		  Joueur = 0;
	          Rafraichir(vide,1);
		}

	      /* Si la case cible contient une pièce adverse */
	      else
		{	  		  
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }

	  /* Déplacement de deux cases */
	  else if(fabs(arrive - depart) == 16 && arrive < depart)
	    {
	      for(i = 0; i < 8; i=i+1)
		{
		  if(CasePionBlancs[i] == depart)
		    {
		      if(strcmp(Piece[depart-9], "  ") == 0 && strchr(sommet(PileCible), 'N') == NULL)
			{
			  Piece[depart - 1] = "  ";
			  Piece[arrive - 1] = "PB";
			  PopAndPush(0);
			  PopAndPush(1);
			  
			  CoupRestant = CoupRestant - 1;
			   if(CoupRestant != 0)
			     Deplacement(0);
			    Joueur = 0;
			    Rafraichir(vide,1);
			}
		      
		      else if(strchr(sommet(PileCible), 'N') != NULL)
			{
			  printf("Coup illegal : la case contient une piece adverse\n");
			  MovePiece(); 
			}
		      else if(strcmp(Piece[depart-9], "  ") != 0)
			{
			  printf("Coup illegal : vous ne pouvez pas passer au dessus des pieces\n");
			  MovePiece();
			}
		       printf("Coup illegal : Ce pion a deja ete joué\n");
		       MovePiece(); 
		    }
		}   
	    }
	  else
	    {
	     printf("Coup illegal : Le pion ne peut pas se deplacer comme ca\n");
	      MovePiece(); 
	    }
	}
      /* Si la case devant le pion contient une pièce adverse */
      else if((abs(arrive - depart) == 7 ||  abs(arrive - depart) == 9) && abs(la - ld) == 1)
	{
	  /* Déplacement diagonale montante */
	  if(abs(arrive - depart) == 7 && strchr(Piece[arrive-2], 'N') != NULL && arrive < depart)
	    {
	      if(strcmp(Piece[arrive - 1], "  ") == 0 || strchr(sommet(PileCible), 'B') != NULL)
		{
		  Piece[depart - 1] = "  ";
		  k=0;
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[0][i] == arrive)
			k = 1;
		    }

		  if(k == 0)
		    Piece[arrive - 1] = "PB";
		  else
		    Piece[arrive - 1] = "DB";

		  PopAndPush(0);
		  PopAndPush(1);
		  
		  CoupRestant = CoupRestant - 1;
		  if(CoupRestant != 0)
		    Deplacement(0);
		  
		  Joueur = 0;
		  Rafraichir(vide,1);		  
		}
	      else if(strchr(sommet(PileCible), 'N') != NULL)
		{
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }

	  /* Déplacement diagonale descendante */
	  else if(abs(arrive - depart) == 9 && strchr(Piece[arrive], 'N') != NULL && arrive < depart && abs(la - ld) == 1)
	    {
	      if(strcmp(Piece[arrive - 1], "  ") == 0 || strchr(sommet(PileCible), 'B') != NULL)
		{
		  Piece[depart - 1] = "  ";
		  k=0;
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[0][i] == arrive)
			k = 1;
		    }

		  if(k == 0)
		    Piece[arrive - 1] = "PB";
		  else
		    Piece[arrive - 1] = "DB";

		  PopAndPush(0);
		  PopAndPush(1);
		  
		  CoupRestant = CoupRestant - 1;
		  if(CoupRestant != 0)
		    Deplacement(0);
		  
		  Joueur = 0;
		  Rafraichir(vide,1);	
		  
		}
	      else if(strchr(sommet(PileCible), 'N') != NULL)
		{
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }
	}
    }
  
  /* Si les noirs jouent actuellement */
  /* même structure de code que pour les pions blancs */
  else
    {
      if(fabs(arrive - depart) == 8 || fabs(arrive - depart) == 16)
	{
	  if(fabs(arrive - depart) == 8 && arrive > depart)
	    {
	      if(strcmp(Piece[arrive - 1], "  ") == 0 || strchr(sommet(PileCible), 'N') != NULL)
		{
		  Piece[depart - 1] = "  ";
		  k=0;
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[7][i] == arrive)
			k = 1;
		    }

		  if(k == 0)
		    Piece[arrive - 1] = "PN";
		  else
		    Piece[arrive - 1] = "DN";
		    
		  PopAndPush(0);
		  PopAndPush(1);
		  
		  CoupRestant = CoupRestant - 1;
		  if(CoupRestant != 0)
		    Deplacement(0);
		  
		  Joueur = 1;
		  Rafraichir(vide,1);
		}
	      else if(strchr(sommet(PileCible), 'B') != NULL)
		{
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }
	  else if(fabs(arrive - depart) == 16 && arrive > depart)
	    {
	      for(i = 0; i < 8; i=i+1)
		{
		  if(CasePionNoirs[i] == depart)
		    {
		      if(strcmp(Piece[depart+7], "  ") == 0 && strchr(sommet(PileCible), 'B') == NULL)
			{
			  Piece[depart - 1] = "  ";
			  Piece[arrive - 1] = "PN";
		          PopAndPush(0);
		          PopAndPush(1);
		  
	         	  CoupRestant = CoupRestant - 1;
		          if(CoupRestant != 0)
			    Deplacement(0);
		  
		          Joueur = 1;
		          Rafraichir(vide,1);
			 
			}
		      else if(strchr(sommet(PileCible), 'B') != NULL)
			{
			  printf("Coup illegal : La case contient une piece adverse\n");
			  MovePiece();
			}
		    }
		}
	      printf("Coup illegal : Ce pion a deja ete joué\n");
	      MovePiece();
	    }
	}
      else if((abs(arrive - depart) == 7 ||  abs(arrive - depart) == 9) && abs(la - ld) == 1)
	{
	  if(abs(arrive - depart) == 7 && strchr(Piece[arrive], 'B') != NULL && arrive > depart)
	    {
	      if(strcmp(Piece[arrive -1], "  ") == 0 || strchr(sommet(PileCible), 'N') != NULL)
		{
		  Piece[depart - 1] = "  ";
		  k=0;
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[7][i] == arrive)
			k = 1;
		    }

		  if(k == 0)
		    Piece[arrive - 1] = "PN";
		  else
		    Piece[arrive - 1] = "DN";

		   PopAndPush(0);
		   PopAndPush(1);
		  
	           CoupRestant = CoupRestant - 1;
		   if(CoupRestant != 0)
		     Deplacement(0);
		  
		   Joueur = 1;
		   Rafraichir(vide,1);
		}
	      else if(strchr(sommet(PileCible), 'B') != NULL)
		{
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }
	  else if(abs(arrive - depart) == 9 && strchr(Piece[arrive-2], 'B') != NULL && arrive > depart && abs(la - ld) == 1)
	    {
	      if(strcmp(Piece[arrive-1], "  ") == 0 || strchr(sommet(PileCible), 'N') != NULL)
		{
		  Piece[depart - 1] = "  ";
		  k=0;
		  for(i = 0; i < 8; i=i+1)
		    {
		      if(Coordonnees[7][i] == arrive)
			k = 1;
		    }

		  if(k == 0)
		    Piece[arrive - 1] = "PN";
		  else
		    Piece[arrive - 1] = "DN";

		   PopAndPush(0);
		   PopAndPush(1);
		  
	           CoupRestant = CoupRestant - 1;
		   if(CoupRestant != 0)
		     Deplacement(0);
		  
		   Joueur = 1;
		   Rafraichir(vide,1);
		  
		}
	      else if(strchr(sommet(PileCible), 'B') != NULL)
		{
		  printf("Coup illegal : La case contient une piece adverse\n");
		  MovePiece();
		}
	    }
	}
    }

  printf("Coup illegal : Ce pion ne peut pas se deplacer comme ça\n");
  MovePiece();
}

/*
@ requires : Rien.
@ assigns : ld,la,cd,ca,Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/

void MoveTour()
{
  int i;
  int j;

  int k;
   
  int ld;
  int cd;

  int la;
  int ca;

  /* Permet de déterminer les lignes et colonnede départ et d'arrivée */
   for(i = 0 ; i < 8 ; i = i+1)
     {
     for(j = 0 ; j < 8 ; j = j+1)
       {
	 if(Coordonnees[i][j] == depart)
	   {
	     ld = i+1;
	     cd = j+1;
	   }
	 if(Coordonnees[i][j] == arrive)
	   {
	     la = i+1;
	     ca = j+1;
	   }
       }
     }

   /* Si la tour se déplace horizontalement */
   if(fabs (arrive - depart) < 8 && la == ld)
     {
       if(depart < arrive)
	 {
	   /* On regarde si la tour ne passe pas au dessus d'autres pièces */
	   for(k = depart ; k < arrive -1 ; k=k+1)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); /* On demande de rentrer une nouvelle case cible */
		 }
	     }  
	 }
       else if(depart > arrive)
	 {
	   for(k = arrive ; k < depart -1 ; k=k+1)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       /* Si c'est au tour des blancs et que : 
            1- la case d'arrivée est vide ou contient au moins une pièce blanche 
            2- la case d'arrivée contient au moins une pièce noire et je déplace plus de pièce qu'il n'y a de pièces noires*/
       if(Joueur == 1 && ((strchr(sommet(PileCible), 'B') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'N') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	       Piece[depart - 1] = "  ";

	       /* Si on déplace une tour */
	       if(strchr(sommet(currentPile), 'T') != NULL)
		  Piece[arrive - 1] = "TB";
	       
	       /* Si on déplace une dame */
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DB";

	       /* Si on déplce un roi et que l'on se déplace d'une case */
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 1)
		 Piece[arrive - 1] = "RB";

	       PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 0;
	       Rafraichir(vide,1); 
	 }
       /* Si c'est au tour des noirs et que : 
            1- la case d'arrivée est vide ou contient au moins une pièce noires 
            2- la case d'arrivée contient au moins une pièce blanche et je déplace plus de pièce qu'il n'y a de pièces noires*/
       else if(Joueur == 0 && ((strchr(sommet(PileCible), 'N') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'B') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	       Piece[depart - 1] = "  ";

	       if(strchr(sommet(currentPile), 'T') != NULL)
		  Piece[arrive - 1] = "TN";
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DN";
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 1)
		 Piece[arrive - 1] = "RN";

	       PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 1;
	       Rafraichir(vide,1);   
	 }
       
       else
	 {	
	   printf("Coup illegal : la case contient une piece adverse\n");
	   MovePiece(); 
	 }
       
     }

   /* Si on déplce la tour verticalement */
   else if(fabs (arrive - depart) >= 8 && ca == cd)
     {
       if(depart < arrive)
	 {
	   for(k = depart+7 ; k < arrive-1 ; k=k+8)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       else if(depart > arrive)
	 {
	   for(k = arrive+7 ; k < depart -1 ; k=k+8)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }

       if(Joueur == 1 && ((strchr(sommet(PileCible), 'B') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'N') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 8)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	      
	   Piece[depart - 1] = "  ";
	   
	   if(strchr(sommet(currentPile), 'T') != NULL)
	      Piece[arrive - 1] = "TB";
	   
	   if(strchr(sommet(currentPile), 'D') != NULL)
	     Piece[arrive - 1] = "DB";
	   
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 8)
	     Piece[arrive - 1] = "RB";

	   PopAndPush(0);
	   PopAndPush(1);
	   CoupRestant = CoupRestant - 1;
	   if(CoupRestant != 0)
	      Deplacement(0);
	       
	   Joueur = 0;
	   Rafraichir(vide,1);  
	 }
       
       else if(Joueur == 0 && ((strchr(sommet(PileCible), 'N') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'B') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 8)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	   
	   Piece[depart - 1] = "  ";

	   if(strchr(sommet(currentPile), 'T') != NULL)
	      Piece[arrive - 1] = "TN";
	   if(strchr(sommet(currentPile), 'D') != NULL)
	     Piece[arrive - 1] = "DN";
	   
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 8)
	       Piece[arrive - 1] = "RN";

	   PopAndPush(0);
	   PopAndPush(1);
	   CoupRestant = CoupRestant - 1;
	   if(CoupRestant != 0)
	      Deplacement(0);
	       
	   Joueur = 1;
	   Rafraichir(vide,1);  
	 }
       
       else
	 {	
	   printf("Coup illegal : la case contient une piece adverse\n");
	   MovePiece(); 
	 }
     }
   
   /* Messages d'erreurs si on tente de déplacer les pièces illégalement */
   if(strchr(sommet(currentPile), 'T') != NULL)
     printf("Coup illegal : La tour ne peut pas se deplacer de cette maniere\n");
   if(strchr(sommet(currentPile), 'D') != NULL)
     printf("Coup illegal : La dame ne peut pas se deplacer de cette maniere\n");
   if(strchr(sommet(currentPile), 'R') != NULL)
     printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
   
   MovePiece(); /* On demande au joueur de choisir une nouvelle case cible */
 }


/*
@ requires : Rien.
@ assigns : Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/
void MoveFou()
{
   int k;

   /* déplacement en diagonale descendante */
   if((int)fabs(arrive - depart) % 9 == 0)
     {
       if(depart < arrive)
	 {
	   /* On vérifie que la pièce ne passe pas au dessus d'autres pièces */
	   for(k = depart + 8 ; k < arrive-1 ; k = k + 9)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       else if(depart > arrive)
	 {
	   for(k = arrive + 8 ; k < depart-1 ; k = k + 9)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       
       /* Si c'est au tour des blancs et que : 
            1- la case d'arrivée est vide ou contient au moins une pièce blanche 
            2- la case d'arrivée contient au moins une pièce noire et je déplace plus de pièce qu'il n'y a de pièces noires */
       if(Joueur == 1 && ((strchr(sommet(PileCible), 'B') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'N') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 9)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	       Piece[depart - 1] = "  ";

	       if(strchr(sommet(currentPile), 'F') != NULL)
		  Piece[arrive - 1] = "FB";
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DB";
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 9)
		 Piece[arrive - 1] = "RB";

	       PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 0;
	       Rafraichir(vide,1); 	 
	 }
       
       else if(Joueur == 0 && ((strchr(sommet(PileCible), 'N') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'B') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 9)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	       Piece[depart - 1] = "  ";

	       if(strchr(sommet(currentPile), 'F') != NULL)
		  Piece[arrive - 1] = "FN";
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DN";
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 9)
		 Piece[arrive - 1] = "RN";

	       PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 1;
	       Rafraichir(vide,1); 	   
	 }
       else
	 {
	   printf("Coup illegal : la case contient une piece adverse\n");
	   MovePiece();  
	 }
       
     }
   
   /* déplacement en diagonale montante */
   else if((int)fabs(arrive - depart) % 7 == 0)
     {
       if(depart < arrive)
	 {
	   for(k = depart + 6 ; k < arrive-1 ; k = k + 7)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       else if(depart > arrive)
	 {
	   for(k = arrive + 6 ; k < depart-1 ; k = k + 7)
	     {
	       if(strcmp(Piece[k], "  ") != 0)
		 {
		   printf("Coup illegal : vous ne pouvez pas passer au dessus d'une piece\n");
		   MovePiece(); 
		 }
	     }
	 }
       if(Joueur == 1 && ((strchr(sommet(PileCible), 'B') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'N') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 7)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	   
	       Piece[depart - 1] = "  ";

	       if(strchr(sommet(currentPile), 'F') != NULL)
		  Piece[arrive - 1] = "FB";
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DB";
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 7)
		 Piece[arrive - 1] = "RB";

	        PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 0;
	       Rafraichir(vide,1); 
	 }
       
       else if(Joueur == 0 && ((strchr(sommet(PileCible), 'N') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'B') != NULL && PieceDeplace > TaillePile(PileCible))))
	 {
	   if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) != 7)
	     {
	       printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
	       MovePiece();
	     }
	       Piece[depart - 1] = "  ";

	       if(strchr(sommet(currentPile), 'F') != NULL)
		  Piece[arrive - 1] = "FN";
	       if(strchr(sommet(currentPile), 'D') != NULL)
		  Piece[arrive - 1] = "DN";
	       if(strchr(sommet(currentPile), 'R') != NULL && fabs (arrive - depart) == 7)
		 Piece[arrive - 1] = "RN";

	       PopAndPush(0);
	       PopAndPush(1);
	       CoupRestant = CoupRestant - 1;
	       if(CoupRestant != 0)
		 Deplacement(0);
	       
	       Joueur = 1;
	       Rafraichir(vide,1); 
	 }
       else
	 {
	   printf("Coup illegal : la case contient une piece adverse\n");
	   MovePiece();  
	 }
     }

   if(strchr(sommet(currentPile), 'F') != NULL)
     printf("Coup illegal : Le fou ne peut pas se deplacer de cette maniere\n");
   if(strchr(sommet(currentPile), 'D') != NULL)
     printf("Coup illegal : La dame ne peut pas se deplacer de cette maniere\n");
   if(strchr(sommet(currentPile), 'R') != NULL)
     printf("Coup illegal : Le Roi ne peut pas se deplacer de cette maniere\n");
   
   MovePiece();
}


/*
@ requires : MoveTour() et MoveFou().
@ assigns : ld,la,cd,ca,Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/

void MoveDameEtRoi()
{
  int i;
  int j;
   
  int ld;
  int cd;

  int la;
  int ca;

  /* même commentaire que pour la tour */
  for(i = 0 ; i < 8 ; i = i+1)
    {
     for(j = 0 ; j < 8 ; j = j+1)
       {
	 if(Coordonnees[i][j] == depart)
	   {
	     ld = i+1;
	     cd = j+1;
	   }
	 if(Coordonnees[i][j] == arrive)
	   {
	     la = i+1;
	     ca = j+1;
	   }
       }
    }

  /* Si on se déplace comme une tour */
  if((fabs (arrive - depart) < 8 && la == ld) || (fabs (arrive - depart) >= 8 && ca == cd))
     {
       MoveTour(); /* On lance la fonction de déplacement de la tour */
     }

  /* Si on se déplace comme un fou */
  else if((int)fabs(arrive - depart) % 9 == 0 || (int)fabs(arrive - depart) % 7 == 0)
     {
       MoveFou(); /* On lance la fonction de déplacement du fou */
     }

  /* Si le déplacement de la dame ou du roi est illégal */
  
  if(strchr(sommet(currentPile), 'D') != NULL)
    {
      printf("Coup illegal : La Dame ne peut pas se deplacer comme ça\n");
      MovePiece();
    }
    else if(strchr(sommet(currentPile), 'R') != NULL)
    {
      printf("Coup illegal : Le Roi ne peut pas se deplacer comme ça\n");
      MovePiece();
    }   
}

/*
@ requires : Rien.
@ assigns : Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/

void MoveCavalier()
{
  /* Si on est respecte l'une des conditions pour que le déplacement soit légal */
  if(fabs (arrive - depart) == 6 || fabs (arrive - depart) == 10 || fabs (arrive - depart) == 15 || fabs (arrive - depart) == 17)
    
    {
      if(Joueur == 1 && ((strchr(sommet(PileCible), 'B') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'N') != NULL && PieceDeplace > TaillePile(PileCible))))
	{
	  Piece[depart - 1] = "  ";
	  Piece[arrive - 1] = "CB";

	  PopAndPush(0);
	  PopAndPush(1);
	  CoupRestant = CoupRestant - 1;
	  if(CoupRestant != 0)
	    Deplacement(0);

	  Joueur = 0;
	   Rafraichir(vide,1); 
	 }

      else if(Joueur == 0 && ((strchr(sommet(PileCible), 'N') != NULL || strcmp(Piece[arrive -1], "  ") == 0) || (strchr(sommet(PileCible), 'B') != NULL && PieceDeplace > TaillePile(PileCible))))
	{
	  Piece[depart - 1] = "  ";
	  Piece[arrive - 1] = "CN";

	  PopAndPush(0);
	  PopAndPush(1);
	  CoupRestant = CoupRestant - 1;
	  if(CoupRestant != 0)
	    Deplacement(0);

	  Joueur = 1;
	  Rafraichir(vide,1);
	}
      else
	{
	  printf("Coup illegal : la case contient une piece adverse\n");
	  MovePiece();
	}
    }
  else
    {
      printf("Coup illegal : Le Cavalier ne peut pas se deplacer comme ça\n");
      MovePiece();
    }
}

/*
@ requires : Entier i >= 0.
@ assigns : Piece,CoupRestant,Joueur.
@ ensures : Rien.
*/

void PopAndPush(int i)
{
  int j = 0;
  
  if(i == 0) /* on décide de désempiler */
    {
      while(strcmp(&coup,Echiquier[j]) != 0)
	{
	  j=j+1;
	}
      pop(&T[j]); /* on désempile la pile de départ */

      /* Si la pile de départ, on affiche son nouveau sommet sur le plateau de jeu */
      if(!is_empty(T[j]))
	Piece[depart - 1] = sommet(T[j]);
      
    }
  else /* on décide d'empiler */
    {
      while(strcmp(&cible,Echiquier[j]) != 0)
	{
	  j=j+1;
	}

      /* Si on respecte la condition pour prendre des pièces de l'adversaire et que :
           1- Les blancs jouent et la case cible contient au moins une pièce noire
           OU
           2- Les noirs jouent et la case cible contient au moins une pièce blanche
      */
      if(PieceDeplace > TaillePile(T[j]) && ((Joueur == 1 && strchr(sommet(T[j]), 'N') != NULL) || (Joueur == 0 && strchr(sommet(T[j]), 'B') != NULL)))
	{
	  /* On vide la pile qui contient les pièces de l'adversaire */
	  while(!is_empty(T[j]))
	    {
	      pop(&T[j]);

	      /* On met à jour le nombre de pièce restante */
	      if(Joueur == 1)
		PieceNrestantes =  PieceNrestantes-1; 
	      else
		PieceBrestantes =  PieceBrestantes-1;		    
	    }
	}

      /* Si un pion s'est transfomé en dame */
      if(Joueur == 1 && k != 0)
	{
	  PieceBrestantes = PieceBrestantes + 1;
	  push("DB",&T[j]);
	}
      else if(Joueur == 0 && k != 0)
	{
	  PieceNrestantes = PieceNrestantes + 1;
	  push("DN",&T[j]);
	}

      /* Sinon en empile normalement*/
      else
	{
	  push(sommet(currentPile),&T[j]);  
	}
    }
}


int main()
{
  printf("\n");
  Initialisation(); /* On lance le jeu avec la fonction initialisation */
  return 0;
} 
