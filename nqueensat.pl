%%%%%%%%%%%%%%%%%%%%%
% N QUEENS PROBLEM
% Created by Daniel Re & Luis Leon on 2019
% Copyright © 2019 Daniel Re & Luis Leon. All rights reserved.

%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):- write('SAT!!'),nl,!.
sat(CNF,I,M):- decideix(CNF,LIT), simlipf(LIT,CNF,CNFS), sat(CNFS,[LIT|I],M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...

decideix(F,LIT):- member([LIT],F),!.  % propagacio unitaria
decideix([[LIT|_]|_],LIT).            % primer element de la primera clausula
decideix([[LIT|_]|_],RES):- RES is -LIT.   % altrament la negacio

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...

simlipf(LIT, F, FS):- LITERAL is (LIT * -1), eliminaClausules(LIT,F,RES), eliminaLiterals(LITERAL,RES,FS).


%%%%%%%%%%%%%%%%%%%%%
% treu(X,L1,L2)
% Donat un literal X i una llista de literals L1,
% -> el tercer parametre sera la llista L1 sense
% - el literal X

treu(X,[],[]):- !.
treu(X,[X|L1],L2):- !, treu(X,L1,L2).
treu(X,[T|L1],Y):- !, treu(X,L1,Y2), append([T],Y2,Y).


%%%%%%%%%%%%%%%%%%%%%
% eliminaClausules(LIT, L1, L2)
% Donat un literal LIT i una CNF L1
% -> el tercer parametre sera la CNF L1
% - sense les clausules que continguin LIT

eliminaClausules(LIT,[],[]).
eliminaClausules(LIT,[X|L1],L2):- member(LIT,X), eliminaClausules(LIT,L1,L2),!.
eliminaClausules(LIT, [Y|L1], L2):- eliminaClausules(LIT,L1,RES), append([Y],RES,L2),!.


%%%%%%%%%%%%%%%%%%%%%
% eliminaLiterals(LIT, L1, L2)
% Donat un literal LIT i una CNF L1
% -> el tercer parametre sera la CNF L1
% - amb les clausules sense el literal LIT

eliminaLiterals(_, [],[]).
eliminaLiterals(LIT,[X|L1],L2):- \+ member(LIT,X), eliminaLiterals(LIT,L1,RES), append([X],RES,L2), !.
eliminaLiterals(LIT,[X|L1],L2):- member(LIT,X),length(X,LENX), LENX > 1, treu(LIT,X,RES), eliminaLiterals(LIT,L1,RES2), append([RES],RES2,L2), !.

%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...

comaminimUn(XS, CNF):- append([],[XS],CNF).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% ...

comamoltUn(XS, CNF):- parelles(XS, R), append([],R,CNF).

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ...

exactamentUn(XS, CNF) :- comamoltUn(XS,RES), append([XS],RES,CNF).

%%%%%%%%%%%%%%%%%%%%%
% negar(X,Y)
% Donat un literal X
% -> el segon parametre sera el negat de X

negar(X, Y) :- Y is X * - 1.

%%%%%%%%%%%%%%%%%%%%%
% parellaNegada(X, L, L2)
% Donat un literal X i una llista L
% -> El tercer parametre es la construcció
% - de una llista de parelles amb X i cada element
% - de L en negatiu
% p.ex parellaNegada(3,[1,2,3],L).
% L = [[-3,-1],[-3,-2],[-3,-3]]

parellaNegada(X, [Y], [[Z,T]]) :- negar(X,Z), negar(Y,T), !.
parellaNegada(X, [Y|SEG], R) :- parellaNegada(X, SEG, R2), negar(X,Z), negar(Y,T), append([[Z,T]], R2, R).

%%%%%%%%%%%%%%%%%%%%%
% parelles(L,L2)
% Donada una llista L
% -> el segon parametre sera una llista
% - de parelles amb tots els elements de la
% - llista L sense repeticions i en negatiu
% p.ex parelles([4,5,6],L).
% L = [[-4,-5],[-4,-6],[-5,-6]]

parelles([_], []) :- !.
parelles([X|SEG], R) :- parellaNegada(X, SEG, R1), parelles(SEG,R2), append(R1,R2,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides
% ...

fesTauler(N,PI,PP,V,I):- ferVars(N,V), fesInicials(PI,PP,N,I), !.

%%%%%%%%%%%%%%%%%%%%%
% ferVars(N,RES)
% Donada una mida N  de tauler
% -> el segon parametre sera una llista de llistes
% - de variables booleanes per representar el tauler

ferVars(N, RES):- N2 is N * N, llista(1, N2, L), trosseja(L, N, RES).

%%%%%%%%%%%%%%%%%%%%%
% fesInicials(PI,PP,N,RES)
% Donada una llista de posicions inicials PI,
% una llista de posicions prohibides PP i una
% mida N de tauler
% -> el quart parametre sera una CNF amb
% - literals unitaris positius de PI i literals unitaris
% - negatius de PP

fesInicials(PI,PP, N, RES):- fixa(PI,N,R1), prohibeix(PP,N,R2), append(R1,R2,RES).

%%%%%%%%%%%%%%%%%%%%%
% actReines(L,L2,RES)
% Donada una llista de llistes L amb tots els elements negatius i una llista L2
% -> el tercer parametere sera la llista L amb els valors de L2 passats a positius
% - per representar que hi ha una reina

actReines(L,[],L).
actReines(L, [X|XS], RES):- XNEG is (X * -1), actReines(L, XS, AUX1), replace(AUX1,XNEG,X,RES).

%%%%%%%%%%%%%%%%%%%%%
% replace(L,LIT1, LIT2,RES)
% Donada una llista L, un literal LIT1 i un literal LIT2
% -> el quart parametre és la llista L amb tots els elements
% - LIT1  canviats per LIT2

replace([],_,_,[]).
replace([X|XS],N,V,[X|L]):- X\=N, replace(XS,N,V,L), !.
replace([X|XS],N,V,[V|L]):- X==N, replace(XS,N,V,L), !.

%%%%%%%%%%%%%%%%%%%%%
% llistaNegativa(L,L2)
% Donada una llista L
% -> el segon parametre sera 
% - la llista L amb tots els elements negats

llistaNegativa([],[]).
llistaNegativa([X|XS],L2):- AUX is X * -1, llistaNegativa(XS,RES), append([AUX],RES,L2).

% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros dinici a fi
% ...

llista(I,I,[I]).
llista(I,F,[I|L]):- I < F, I1 is I+1, llista(I1,F,L).

% AUX
% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (Sassumeix que la llargada de L i N ho fan possible)
% ...

trosseja([], _, []).
trosseja(L, N, [X|XS]) :- length(X, N), append(X, AUX, L), trosseja(AUX, N, XS).

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
% ...

fixa([],_,[]).
fixa([(A,B)|XS],N,F):- VAR is ((A*N)-N)+B, fixa(XS,N,RES), append([[VAR]],RES,F).

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
% ...

prohibeix([],_,[]).
prohibeix([(A,B)|XS],N,F):- VAR is (((A*N)-N)+B) * -1, prohibeix(XS,N,RES), append([[VAR]],RES,F).

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no samenecen les reines de les mateixes files
% ...

noAmenacesFiles([],[]).
noAmenacesFiles([X|XS], CNF):- comamoltUn(X,RES), noAmenacesFiles(XS,RES2), append(RES, RES2, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%
% transposaMatriu(M,MT)
% Donada una llista de llistes M que representa una matriu
% -> el segon parametre sera la matriu M transposada

transposaMatriu([[]|_], []):-!.
transposaMatriu(M, [F|FS]) :- transposaColumna(M, F, RES), transposaMatriu(RES, FS).

%%%%%%%%%%%%%%%%%%%%%
% transposaColumna(M,F,RES)
% Donada una matriu M
% -> el segon parametre sera la primera
% - columna de la matriu M
% -> el tercer parametre sera la matriu M
% - sense la primera columna

transposaColumna([], [], []).
transposaColumna([[H|T]|FS], [H|HS], [T|TS]) :- transposaColumna(FS, HS, TS).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no samenecen les reines de les mateixes columnes
% ...

noAmenacesColumnes(V,F):- transposaMatriu(V,AUX), noAmenacesFiles(AUX,F).

% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES ALTRES
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no samenecen les reines de les mateixesdiagonals

noAmenacesDiagonals(N,D):- diagonals(N,L), llistesDiagonalsAVars(L,N,VARS), comamoltUnVars(VARS,D).

%%%%%%%%%%%%%%%%%%%%%
% comamoltUnVars(L,RES)
% Donada una CNF L
% -> el segon parametre sera una CNF que codifiqui
% - com a molt un positiu

comamoltUnVars([],[]).
comamoltUnVars([X|XS], RES):- comamoltUn(X,AUX), comamoltUnVars(XS,AUX2), append(AUX,AUX2,RES).

%%%%%%%%%%%%%%%%%%%%%
% diagonals(N,L)
% Genera les llistes de diagonals duna matriu NxN. Cada diagonal es una
% llista de coordenades.

diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L),!.

%%%%%%%%%%%%%%%%%%%%%
% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=< N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).


%%%%%%%%%%%%%%%%%%%%%
% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonals2In(1,3,L).
% L = [[(3, 1)],[(3, 2),(2, 1)],[(3, 3),(2, 2),(1, 1)],[(2, 3),(1, 2)],[(1, 3)]] 
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonals2In(D,N,[]):- D is 2*N,!.
diagonals2In(D,N,[L1|L]):- D =< N,fesDiagonal2(N,D,L1), D1 is D+1, diagonals2In(D1,N,L).
diagonals2In(D,N,[L1|L]):- D > N, F is (N-(D-N)), fesDiagonalReves2(F,N,N,L1), D1 is D+1, diagonals2In(D1,N,L).

fesDiagonal2(F,1,[(F,1)]):- !.
fesDiagonal2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonal2(F1,C1,R).

fesDiagonalReves2(1,C,_,[(1,C)]):-!.
fesDiagonalReves2(F,C,N,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonalReves2(F1,C1,N,R).

%%%%%%%%%%%%%%%%%%%%%
% coordenadesAVars(C,N,R).
% donada una llista de coordenades, C dun tauler NxN.
% donada la mida N de tauler.
% -> R sera la llista de les variables corresponents a les posicions en el tauler de NxN.

coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

%%%%%%%%%%%%%%%%%%%%%
% llistesDiagonalsAVars(LP,N,LV).
% donada una llista de llistes de posicions que representen les diagonals LP,
% donada la mida N
% -> LV sera una llista de llistes de variables, on cada variable representa la posicio en el tauler
% -> LV no mostrara les diagonals que tinguin una casella, es a dir la de les cantonades

llistesDiagonalsAVars([],_,[]).
llistesDiagonalsAVars([X|XS],N,L):- \+ length(X,1), coordenadesAVars(X,N,RES), llistesDiagonalsAVars(XS,N,L2), append([RES],L2,L),!.
llistesDiagonalsAVars([X|XS],N,L):- llistesDiagonalsAVars(XS,N,L).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment dun tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha dhaver exactament N reines al tauler
% per n = 2 i n = 3 el numero maxim de reines es n-1, altrament es n

minimNReines([],[]).
minimNReines([X|XS], RES):- exactamentUn(X,AUX), minimNReines(XS, AUX2), append(AUX,AUX2,RES).

%%%%%%%%%%%%%%%%%%%%%
% llegeixDades(N,R,PP)
% -> els tres parametres seran els llegits
% - en lentrada per teclat per part de lusuari

llegeixDades(N,R,PP):-   write('Entra les dimensions del tauler: ' ),nl, read(N),
                         write('Entra on hi ha reines [(x1,y1),(x2,y2)...]: '),nl, read(R),
                         write('Entra posicions prohibides[(x1,y1),(x2,y2)...]: '),nl, read(PP), get0(C).


%%%%%%%%%%%%%%%%%%%%%
% resol. 
% Ens demana els parametres del tauler i lestat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
% N es la mida del tauler
% R son les posicions inicials on hi ha reines amb el format: [(x1,y1),(x2,y2)...]
% PP son les posicions on esta prohibit posar reines amb el format: [(x1,y1),(x2,y2)...]

resol :- 		llegeixDades(N, R, PP) , fesTauler(N,R,PP,V,I),nl,
                minimNReines(V,FN),
                noAmenacesFiles(V,CNFfiles),
                noAmenacesColumnes(V,CNFcolumnes),
                noAmenacesDiagonals(N,CNFdiagonals),nl,
                append(CNFfiles,CNFcolumnes,CNFfilcol),
                append(CNFfilcol,CNFdiagonals, CNFfilcoldiag),
                append(CNFfilcoldiag, FN, CNFFCD),
                append(CNFFCD, I, CNFFINAL),
                sat(CNFFINAL,[],M),
                mostraTauler2(N,I,M).


%%%%%%%%%%%%%%%%%%
% mostraTauler2(N, I, M)
% Donada la mida del tauler N, variables que representen les posicions de les reines M, restriccions I,
% on I hi han les variables-posicions on hi ha dhaver reines (1,2,3..) 
% i les variables-posicions on no es pot posar reina(...-4,-5..), representat en valors negatius,
% on M es el model trobat, variables on representa les posicions de les reines 
% -> mostra 'O' si era una reina inicial
% -> mostra 'X' si es prohibeix posar una reina
% -> mostra ' ' si esta buit (valor negatiu)
% -> mostra 'Q' si la reina sha decidit amb el model ,
% -> mostra el tauler amb N i les posicions de reines M
% Per exemple:
% | ?- mostraTauler2(5,[[1],[-6],[12],[-19]],[1,9,12,20,23]).
%-----------
%|O| | | | |
%-----------
%|X| | |Q| |
%-----------
%| |O| | | |
%-----------
%| | | |X|Q|
%-----------
%| | |Q| | |
%-----------

mostraTauler2(N,I,M):- ferVarsMostrarTauler(N,M,RES), mostrarFilaGuio(N * 2 + 1), mostrarFiles2(N,I,RES),!.

%%%%%%%%%%%%%%%%%%
% mostrarFiles2(N, I, XS)
% Donada la mida del tauler N, el models I, i la llista de files XS
% -> mostra les files del tauler expresades en XS

mostrarFiles2(_,_,[]):- nl.
mostrarFiles2(N,I,[X|XS]):- mostrarFila2(X,I), nl, mostrarFilaGuio(N * 2 + 1), mostrarFiles2(N,I,XS).

%%%%%%%%%%%%%%%%%%
% mostrarFila2(XS,I)
% Donada una fila del tauler XS, i les restriccions I
% -> mostra 'O' si era una reina inicial
% -> mostra 'X' si es prohibeix posar una reina
% -> mostra ' ' si esta buit (valor negatiu)
% -> mostra 'Q' si la reina sha decidit amb el model

mostrarFila2([],I):- write('|').
mostrarFila2([X|XS],I):- flatten(I,IS), member(X,IS), X > 0, write('|O'), mostrarFila2(XS,I).
mostrarFila2([X|XS],I):- flatten(I,IS), member(X,IS), X < 0, write('|X'), mostrarFila2(XS,I).
mostrarFila2([X|XS],I):- X > 0, write('|Q'), mostrarFila2(XS,I).
mostrarFila2([X|XS],I):- X < 0, write('| '), mostrarFila2(XS,I).

%%%%%%%%%%%%%%%%%%
% mostraTauler(N, M)
% Donada la mida del tauler N, model que son variables que representen les posicions de les reines M, on
% -> mostra el tauler amb N i les posicions de reines M
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------

mostraTauler(N,M):- ferVarsMostrarTauler(N,M,RES), mostrarFilaGuio(N * 2 + 1), mostrarFiles(N,RES).

%%%%%%%%%%%%%%%%%%
% mostrarFilaGuio(N)
% Donada el valor N
% -> mostra les N cops un guio '-'

mostrarFilaGuio(0):- nl,!.
mostrarFilaGuio(N):- write('-'), M is N - 1, mostrarFilaGuio(M).

%%%%%%%%%%%%%%%%%%
% mostrarFiles(N, XS)
% Donada la mida del tauler N, i la llista de files XS
% -> mostra les files del tauler expresades en XS

mostrarFiles(_,[]):- nl, !.
mostrarFiles(N,[X|XS]):- mostrarFila(X), nl, mostrarFilaGuio(N * 2 + 1), mostrarFiles(N,XS).

%%%%%%%%%%%%%%%%%%
% mostrarFila(XS)
% Donada una fila del tauler XS
% -> mostra 'Q' si hi ha reina, ' ' si esta buit (valor negatiu)

mostrarFila([]):- write('|'),!.
mostrarFila([X|XS]):- X > 0, write('|Q'), mostrarFila(XS).
mostrarFila([X|XS]):- X < 0, write('| '), mostrarFila(XS).

%%%%%%%%%%%%%%%%%%
% ferVarsMostrarTauler(N, LIT, RES)
% Donat la mida tauler N, posicions inicial + posicions prohibides, LIT
% -> el tercer parametre sera la representacio del tauler amb reines i llocs lliures

ferVarsMostrarTauler(N, LIT, RES):- N2 is N * N, llista(1, N2, L), llistaNegativa(L, M), actReines(M, LIT, R), trosseja(R, N, RES).
