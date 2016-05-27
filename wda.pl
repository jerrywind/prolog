%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Wang's deductive Algorithm
% Author: jerrywind
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% make operator by op/3
%
:- op(501,fy,neg).
:- op(601,xfy,and).
:- op(701,xfy,or).
:- op(801,xfy,imp).
:- op(901,xfy,iff).
:- op(401,xfy,seq).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prove([L seq R]) , begin to deduction if is a list, split it.
%

prove([F|_]):-
   F = _ seq _,
    prove(H),!.

prove([F|_],LL,RL,P):-
		F = _ seq _,
		LL = [],
		RL = [],
		P = [],
		prove(H,LL,RL,P).
		
		

prove(F,LL,RL,P):-
    F = L seq R,
    LL=[],
    RL=[],
    P=H,
    rules(F,LL,RL,P),!.

prove(1,1,1):-
    nl,write('yes'),!.

printprove(F):-
		prove(H,LL,RL,F),
		nl,write(' Initial rules: left-'),write(LL),write('    right-'),write(RL),
		printstep(P).

printstep([F|R]):-
		nl,
		write(F),
		printstep(R).
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rules(L,R,+LL,+RL) can have 11 condition, first ten is rules, the last one is initial state.
% LL is left literal ,RL is right literal
% RR is right rest, LR is left rest

%% p2a ,  seq neg
rules(F,LL,RL,P):-
		F=L seq [H|RR]
    H = neg X,
    append(F,'    P2A',PH),
    P=[PH|P],
    % nl,write(X),write('   p2a    '),write([X|L]),write(RR),write(LL),write(RL),
    rules([X|L] seq RR,LL,RL,P).
    
%% p2b  , neg seq
rules(F,LL,RL,P):-
		F=[H| LR] seq R,
    H = neg X,
     append(F,'    P2B',PH),
    P=[PH|P],
   % nl,write(X),write('   p2b    '),write(LR),write([X|R]),write(LL),write(RL),
    rules(LR seq [X|R],LL,RL,P).

%% p3a  ,  seq and
rules(F,LL,RL,P):-
		F=L seq [H|RR],
    H=(X and Y),
    append(F,'    P3A',PH),
    P=[PH|P],
    % nl,write(X),write(Y),write('   p3a    '),write(L),write([X|RR]),write(LL),write(RL),
    rules(L seq [X|RR],LL,RL,P),
   %  nl,write('p3a b1 f, b2 s'),
    rules(L seq [Y|RR],LL,RL,P),
   %  nl,write('p3a b2 f').

%% p3b , and seq
rules(F,LL,RL,P):-
		F=[H|LR] seq R,
    H=(X and Y),
    append(F,'    P3B',PH),
    P=[PH|P],
   % nl,write(X),write(Y),write('   p3b    '),write(R),write([X,Y|LR]),write(LL),write(RL),
    rules([X,Y|LR] seq R,LL,RL,P).

%% p4a seq or
rules(F,LL,RL,P):-
		F=L seq [H|RR],
    H=(X or Y),
    append(F,'    P4A',PH),
    P=[PH|P],
    % nl,write(X),write('  '),write(Y),write('   p4a'),write(LL),write(RL),
    rules(L seq [X,Y|RR],LL,RL,P).

%% p4b or seq
rules(F,LL,RL,P):-
		F=[H|LR] seq R,
    H=(X or Y),
    append(F,'    P4B',PH),
    P=[PH|P],
    % nl,write(X),write(Y),write('   p4b'),write(LL),write(RL),
    rules([X|LR] seq R,LL,RL,P,),
    % nl,write('p4b b1 f, b2 s'),
    rules([Y|LR] seq R,LL,RL,P),
    % nl,write('p4b b2 f').

%% p5a seq imp
rules(F,LL,RL,P):-
		F=L seq [H|RR],
    H=(X imp Y),
     append(F,'    P5A',PH),
    P=[PH|P],
    % nl,write(X),write(Y),write('   p5a'),write(LL),write(RL),
    rules([X|L] seq [Y|RR],LL,RL,P).

%% p5b imp seq
rules(F,LL,RL,P):-
		F=[H|LR] seq R,
    H=(X imp Y),
      append(F,'    P5B',PH),
    P=[PH|P],
    % nl,write(X),write(Y),write('   p5b'),write(LL),write(RL),
    rules([Y|LR] seq R,LL,RL,P),
    % nl,write('p5b b1 f, b2 s'),
    rules(LR seq [X|R],LL,RL,P),
    % nl,write('p5b b2 f').

%% p6a seq iff
rules(F,LL,RL,P):-
	 F=L seq [H|RR],
   H=(X iff Y),
   append(F,'    P6A',PH),
   P=[PH|P],
   
   % nl,write(X),write(Y),write('   p6a'),write(LL),write(RL),
   rules([X|L] seq [Y|RR],LL,RL,P),
  % nl,write('p6a b1 f, b2 s'),
   rules([Y|L] seq [X|RR],LL,RL,P),
  % nl,write('p6a b2f').

%% p6b iff seq
rules(F,LL,RL,P):-
	 F=[H|LR] seq R,
   H=(X iff Y),
   append(F,'    P6B',PH),
   P=[PH|P],
   % nl,write(X),write(Y),write('   p6b'),write(LL),write(RL),
   rules(LR,[X,Y|R],LL,RL),
   % nl,write('p6b b1 f, b2 s'),
   rules([X,Y|LR],R,LL,RL),
   % nl,write('p6b b2 f').

%% head is literal ,
%  then if this literal in the leftlist and is a member of the rightliteral, then sequent is true.
%  elsif left and right list is empty ,then if left literal is empty ,that means empty can prove everthing, true.
%  else can not prove this sequent. 
 
rules([H|LR],R,LL,RL):-
   atom(H),
   member(H,RL),!,
   LL=[H|LL],
  % nl,write(H),write('    atom L  yes'),write(LR),write(R),write(LL),write(RL),
  %  nl,write('yes'),
   prove(1,1,1).

rules([H|LR],R,LL,RL):-
   atom(H),
   LH=[H|LL],
   % nl,write(H),write('    atom L'),write(LR),write(R),write(LH),write(RL),
   rules(LR,R,LH,RL).

rules(L,[H|RR],LL,RL):-
   atom(H),
   member(H,LL),!,
   RL=[H|RL],
  % nl,write(H),write('    atom R yes'),write(L),write(RR),write(LL),write(RL),
  % nl,write('yes'),
    prove(1,1,1).

rules(L,[H|RR],LL,RL):-
   atom(H),
   RH=[H|RL],
   % nl,write(H),write('    atom R'),write(L),write(RR),write(LL),write(RH),!,
   rules(L,RR,LL,RH).

rules([],[],[],_):-
   prove(1,1,1).

% rules([],[],LL,RL):-
%   !,
%   nl,write(LL),write(RL),write('false'),prove(false).
