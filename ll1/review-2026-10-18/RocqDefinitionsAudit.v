(* Original attachment definitions through line 223; independent audit proofs follow.
   This audit contains no Admitted declarations or new axioms. *)
Require Import List.
Require Import Notations.
Require Import Logic.
Require Import Recdef.
Import ListNotations.


(* Grammar *)
Record grammar := {
  terminal : Type;
  nonterminal : Type;
  symbol := (terminal + nonterminal)%type;
  symbols : list symbol;
  rule := (nonterminal * list symbol)%type;
  rules : list rule;
  axiom : nonterminal;
  tbeq : (terminal -> terminal -> bool);
  prooftbeq :  forall t t' : terminal, tbeq t t' = true <-> t=t';
  ntbeq : (nonterminal -> nonterminal -> bool);
  proofntbeq : forall N N' : nonterminal, ntbeq N N' = true <-> N=N';
    (*ntbeq : (preuve égalité + preuve inégalité)*)
}.

(*Definition nonterminalbeq (G : grammar) ( N : nonterminal G)  ( M :nonterminal G) : bool :=
Admitted.*)


(* Sentential forms and words *)
Definition word (G : grammar) := list (terminal G).
Definition sentence (G : grammar) := list (symbol G).

Fixpoint first_nonterminal_of_sentence_pos {G : grammar} (s : sentence G) (pos : nat) :=
  match s with
  | [] => None
  | x :: xs => 
    match x with
    | inr _ => Some pos
    | _ => first_nonterminal_of_sentence_pos xs (pos + 1)
    end
  end.

Fixpoint first_nonterminal_of_sentence {G : grammar} (s : sentence G) :=
  match s with
  | [] => None
  | x :: xs => 
    match x with
    | inr N => Some N
    | _ => first_nonterminal_of_sentence xs
    end
  end.

Definition split_sentence {G : grammar} (pos : nat) (s : sentence G) : option (sentence G * nonterminal G * sentence G) :=
  match (nth_error s pos) with
  | None => None
  | Some(x) => match x with
   | inr a => Some ((firstn (pos) s : sentence G),
                    (a : nonterminal G ),
                    (skipn (pos + 1) s : sentence G))
   | inl b => None
   end
  end.

Definition sentence_of_word {G : grammar} (w : word G) : sentence G :=
  List.map inl w.

Definition sentence_of_nonterminal {G : grammar} (nt : nonterminal G) : sentence G :=
  [ inr nt ].

Definition hd' {G : grammar} (l:list (terminal G)) :=
match l with
  | [] => None
  | x :: _ => Some x
end.

(* Definition of w:1 where w:k = wϵ if |w| < k or α if w = αγ and |α| = k. *)
Definition first_terminal_of_words_agree {G : grammar} (v : word G) (v' : word G) :=
  match hd' v, hd' v' with
  | None, None => True (* We let the empty list be the empty word by convention.
                          This corresponds to the case, v = v' = epsilon. *)
  | Some fv, Some fv' => tbeq G fv fv' = true
  | _, _ => False
  end.


(* Rules *)
Definition nonterminal_of_rule {G : grammar} (r : rule G) : nonterminal G :=
  fst r.

Definition rhs_of_rule {G : grammar} (r: rule G): sentence G :=
  snd r.

Definition apply_rule {G : grammar} (pos : nat) (r : rule G) (s : sentence G) : option (sentence G) :=
  match split_sentence pos s with
    | None => None
    | Some (prefix, nt, suffix) =>
      if (ntbeq G nt (nonterminal_of_rule r)) then
        Some (prefix ++ (rhs_of_rule r) ++ suffix)
      else
        None
  end.


(* Derivation *)
Inductive derivation (G : grammar) : Type :=
| EndOfDerivation
| ApplyRule : derivation G -> nat -> rule G -> derivation G.

Inductive derives (G : grammar) : (sentence G) -> (derivation G) -> (sentence G) -> Prop :=
| EmptyDerivation:
  forall s : sentence G,
  derives G s (EndOfDerivation G) s
| ApplyRuleDerivation:
  forall (s1 s2 s3 : sentence G) (d : derivation G) (pos : nat) (r : rule G),
  derives G s1 d s2 ->
  apply_rule pos r s2 = Some s3 ->
  derives G s1 (ApplyRule G d pos r) s3.

Definition recognize (G : grammar) (w : word G) :=
  exists d,
  derives G (sentence_of_nonterminal (axiom G)) d (sentence_of_word w).

Fixpoint apply_derivation {G : grammar} (s : sentence G) (d : derivation G) : option (sentence G) :=
  match d with
  | EndOfDerivation _ => Some s
  | ApplyRule _ d' pos r =>
    match apply_derivation s d' with
    | None => None
    | Some s' => apply_rule pos r s'
    end
  end.


(* Prove apply_derivation correct *)
Lemma apply_derivation_correct (G : grammar):
  forall s1 d s2,
  apply_derivation s1 d = Some s2 -> derives G s1 d s2.
Proof.
  induction d.
  - simpl.
    intros.
    inversion H.
    subst.
    apply EmptyDerivation.
  - simpl.
    destruct (apply_derivation s1 d).
    * intros.
      assert (H' : derives G s1 d s).
      apply IHd.
      reflexivity.
      apply ApplyRuleDerivation with (s2 := s) ; assumption.
    * congruence.
Qed.

Lemma apply_derivation_correct' (G : grammar):
  forall s1 d s2,
  derives G s1 d s2 -> apply_derivation s1 d = Some s2.
Proof.
  intros.
  induction H.
  * simpl.
    auto.
  * simpl.
    rewrite IHderives.
    assumption.
Qed.


(* Left-most derivation *)
Inductive left_derivation (G : grammar) : Type :=
| EndOfLeftDerivation
| ApplyRuleOnLeftNonTerminal : left_derivation G -> (rule G) -> left_derivation G.

Inductive derives_leftmost (G : grammar) : (sentence G) -> (left_derivation G) -> (sentence G) -> Prop :=
| EmptyLeftDerivation:
  forall s : sentence G,
  derives_leftmost G s (EndOfLeftDerivation G) s
| ApplyRuleLeftDerivation:
  forall (s1 s2 s3 : sentence G) (d : left_derivation G) (r : rule G) (pos : nat),
  derives_leftmost G s1 d s2 ->
  (first_nonterminal_of_sentence_pos s2 0) = Some pos ->
  apply_rule pos r s2 = Some s3 ->
  derives_leftmost G s1 (ApplyRuleOnLeftNonTerminal G d r) s3.

Definition derives_one_leftmost_derivation (G : grammar) (s1 : sentence G) (d : left_derivation G) (s2 : sentence G) :=
  forall r pos,
  derives_leftmost G s1 d s2 
  /\ (first_nonterminal_of_sentence_pos s1 0) = Some pos 
  /\ apply_rule pos r s1 = Some s2.

(* Left-recursive grammar *)
(* A grammar is left-recursive if and only if there exists
  a nonterminal symbol A that can derive
  to a sentential form with itself as the leftmost symbol. *)
Definition left_recursive (G : grammar) :=
  exists (A : nonterminal G) d (alpha : sentence G),
  let A' := sentence_of_nonterminal A in
  derives G A' d (A' ++ alpha).


(* LL(1) grammar *)
Definition LL1 (G : grammar) :=
  let A := sentence_of_nonterminal (axiom G) in
  forall
  d0 d1 d1' d2 d2'
  alpha alpha' gamma
  (N : nonterminal G)
  (u : word G) (v : word G) (v' : word G),
  let su := sentence_of_word u in
  let sv := sentence_of_word v in
  let sv' := sentence_of_word v' in
  let intermediate_sentence := (su ++ [inr N] ++ gamma) in

  ((derives_leftmost G A d0 intermediate_sentence
  (* The following derives is the application of the rule N -> alpha: *)
  /\ derives_one_leftmost_derivation G intermediate_sentence d1 (su ++ alpha ++ gamma)
  /\ derives G (su ++ alpha ++ gamma) d2 (su ++ sv))

  /\ (derives_leftmost G A d0 intermediate_sentence
  (* The following derives is the application of the rule N -> alpha': *)
  /\ derives_one_leftmost_derivation G intermediate_sentence d1' (su ++ alpha' ++ gamma)
  /\ derives G (su ++ alpha' ++ gamma) d2' (su ++ sv'))

  /\ first_terminal_of_words_agree v v') -> alpha = alpha'.
Lemma audit_every_grammar_left_recursive (G : grammar) : left_recursive G.
Proof.
  exists (axiom G), (EndOfDerivation G), [].
  simpl. apply EmptyDerivation.
Qed.
Lemma audit_one_leftmost_impossible (G : grammar) s1 d s2 :
  ~ derives_one_leftmost_derivation G s1 d s2.
Proof.
  unfold derives_one_leftmost_derivation. intro H.
  pose proof (H (axiom G, []) 0) as H0.
  pose proof (H (axiom G, []) 1) as H1.
  destruct H0 as [_ [H0 _]].
  destruct H1 as [_ [H1 _]].
  congruence.
Qed.
Lemma audit_every_grammar_LL1 (G : grammar) : LL1 G.
Proof.
  unfold LL1. intros d0 d1 d1' d2 d2' alpha alpha' gamma N u v v'.
  simpl. intro H.
  destruct H as [[_ [Hbad _]] _].
  exfalso. eapply audit_one_leftmost_impossible. exact Hbad.
Qed.

Lemma audit_recognize_any_word (G : grammar) (w : word G) : recognize G w.
Proof.
  unfold recognize. exists (ApplyRule G (EndOfDerivation G) 0 (axiom G, sentence_of_word w)).
  eapply ApplyRuleDerivation.
  - apply EmptyDerivation.
  - unfold apply_rule, split_sentence, sentence_of_nonterminal, nonterminal_of_rule, rhs_of_rule.
    simpl. rewrite (proj2 (proofntbeq G (axiom G) (axiom G)) eq_refl).
    simpl. rewrite app_nil_r. reflexivity.
Qed.
Theorem audit_original_claim_is_impossible
  (original_claim : forall G, left_recursive G -> not (LL1 G)) : False.
Proof.
  pose (G := {| terminal := unit; nonterminal := unit; symbols := []; rules := []; axiom := tt;
    tbeq := fun _ _ => true; prooftbeq := fun a b => conj (fun _ => match a, b with tt, tt => eq_refl end) (fun _ => eq_refl);
    ntbeq := fun _ _ => true; proofntbeq := fun a b => conj (fun _ => match a, b with tt, tt => eq_refl end) (fun _ => eq_refl) |}).
  exact (original_claim G (audit_every_grammar_left_recursive G) (audit_every_grammar_LL1 G)).
Qed.
Print Assumptions audit_every_grammar_left_recursive.
Print Assumptions audit_one_leftmost_impossible.
Print Assumptions audit_every_grammar_LL1.
Print Assumptions audit_recognize_any_word.
Print Assumptions audit_original_claim_is_impossible.
