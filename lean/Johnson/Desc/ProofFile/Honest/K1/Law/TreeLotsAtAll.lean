-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TreeLotsAtAll.lean: THE SHARED "SENDING" (the kind K1): K1's
ENTRIES FOR THE FUNCTION FROM A MEMBER's NUMBER TO ITS TreeLot (ProofFile's Script.ofLots,
Honest/Thread/ScriptLots.lean), OVER A LIST OF JOBS BY NUMBERS. One definition with code; eight
theorems.

WHY. Script.ofLots asks a function tl : Nat → TreeLot at the SENDING member's number. Such a
function stood at our two toys alone (Honest/K1/SeatedToy.lean, treeLots).

  k1TreeLots       at a number of the list: the job's own table by treeTbl
                   (Honest/K1/ScriptLots.lean) and off = 0; at every other number: THE LETTER rest
  k1TreeLots_at    where no number stands in the list twice (hnd): at a member's number, that
                   member's lot
  k1TreeLots_rest  at a number that is not in the list: rest
  ownTrees_at_lots at a thread whose bs, front, table and fixed are those of the Script laid with
                   k1TreeLots (FOUR PREMISES: EQUATIONS BETWEEN THE THREAD's FIELDS AND THE LAID
                   SCRIPT's): ProofFile's form OwnTrees at each member of the list. TWO CALLS:
                   ofLots_ownTrees; k1TreeLots_at. NEVER "OwnTrees IS HAD" WITHOUT THE FOUR
  rest_at_three    a fact: 3 is no number of the 52: there rest answers
  w_lot_bites      A NEGATIVE TEST: over the 51 alone rest answers at 356; over the 52 W's own lot
                   does: so the 52nd entry is read
  first_wins, treeTbl_place, first_wins_parts
                   A NEGATIVE TEST: at a list with one number twice the SECOND entry's number gets
                   the FIRST entry's lot (first_wins); a table's first component is the job's own
                   place, in both arms of treeTbl (treeTbl_place: a public value); SO AT TWO JOBS
                   WHOSE PLANS' PLACES PART k1TreeLots_at's END IS FALSE AT THE SECOND ENTRY
                   (first_wins_parts): hnd cannot be dropped

MIND: A DEFAULT WHERE COINS ARE DUE, INHERITED, NOT NEW. treeTbl's own arm "| none => (J.P.place,
wordlessTable)" answers where lentCut answers nothing: just where the public test bookCovers is
false (lentCut_isSome, Honest/K1/ScriptAtLaw.lean). NO LAW HERE ASKS THAT THE BOOK COVERS THE PART's
COUNT: all are equations between terms and hold at that arm too. WHOEVER SPEAKS OF COINS AT
k1TreeLots OWES "THE BOOK COVERS THE PART's COINS" ((S6) of the riders)
BY NAME.
MIND: List.lookup TAKES THE FIRST OF TWO ENTRIES WITH ONE NUMBER, IN SILENCE. hnd bars it; at the
52: k1MembersW_nodup (LotsAtAll.lean); first_wins_parts is its tooth.
MIND: rest IS A LETTER. WE LAY NO DEFAULT THERE. Whoever lays a term for it brings that term as text
first: a rest that answers (default, wordlessTable) would bring the toy's default back.

THE BOOK. The sentence, to the letter, with its third
arm, in marks: "At a book whose count at the part's address does not cover the part's due this law
holds for nothing, and it is never quoted as if it spoke there: hasCoins is neither asked nor paid
here: whoever quotes this law at a book names hasCoins at that book beside it." OUR OWN WORDS: so at
ownTrees_at_lots: Bk is a letter, and nothing is asked of it: at such a book its end speaks of
treeTbl's wordless table (the first MIND above).

A TreeLot's table is handed all coins and the whole input.

KIN, TOLD. The toy's treeLots (SeatedToy.lean) is this term at the toy's jobs with a default in the
place of rest. k1_ownTreesAt (Honest/K1/OwnTreesK1.lean) reaches OwnTreesAt by play, off the run;
here the table is laid off the data. WHICH ROAD THE FIELD table TAKES IS L25's TO SAY. The law on
List.lookup is the library's (Compile.Batch.lookup_of_mem).

Limits. NO SCRIPT IS LAID HERE: pl, ml, cells, tok and rest are letters. Nothing ties a table to
what a part sends. K1's members alone. Nothing says how a coin is made. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtAll
import Compile.Batch.PrunedFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot OwnTrees ofLots_ownTrees)

variable {Bk : ProverCoinCounts} {Wl Xi X : Type}

/-- **K1's TreeLots, by the member's number.** At a number of the list: the table is the job's own
(treeTbl at chain 0); "fun _ => 0" is TreeLot's second field off: how many of the member's own
challenges a tree's table reads, that is, in which of the member's rounds the tree is sent: A PUBLIC
NUMBER, 0 by k1_sent_first (Honest/K1/OwnTreesK1.lean): NO DEFAULT AT A COIN. At every other number:
the letter rest. -/
def k1TreeLots (wit : Wl → PlaceIn Xi) (own₀ : X) (jobs : List (Nat × SendJob (PlaceIn Xi) X))
    (rest : Nat → TreeLot Bk Wl) (b : Nat) : TreeLot Bk Wl :=
  match jobs.lookup b with
  | some J => ⟨treeTbl 0 wit J own₀, fun _ => 0⟩
  | none => rest b

/-- **At a member's number, that member's lot**, where no number stands in the list twice. -/
theorem k1TreeLots_at (wit : Wl → PlaceIn Xi) (own₀ : X)
    {jobs : List (Nat × SendJob (PlaceIn Xi) X)} (rest : Nat → TreeLot Bk Wl)
    (hnd : (jobs.map (·.1)).Nodup) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    k1TreeLots wit own₀ jobs rest x.1 = ⟨treeTbl 0 wit x.2 own₀, fun _ => 0⟩ := by
  unfold k1TreeLots
  rw [Compile.Batch.lookup_of_mem jobs hnd x hx]

/-- **At a number that is not in the list: rest.** -/
theorem k1TreeLots_rest (wit : Wl → PlaceIn Xi) (own₀ : X)
    {jobs : List (Nat × SendJob (PlaceIn Xi) X)} (rest : Nat → TreeLot Bk Wl) {b : Nat}
    (hb : b ∉ jobs.map (·.1)) : k1TreeLots wit own₀ jobs rest b = rest b := by
  have e : jobs.lookup b = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    rw [bne_iff_ne]
    intro e
    exact hb (e ▸ List.mem_map_of_mem hp)
  unfold k1TreeLots
  rw [e]

/-- **ProofFile's FORM OwnTrees AT EACH MEMBER OF THE LIST**, at a thread whose four fields are the laid
Script's. -/
theorem ownTrees_at_lots {V X' Pb Cells Tok : Type} {cF : Chain S ProofFile.Cl} (front : Nat)
    (cells : Wl → Cells) (tok : Wl → Tok) (pl : List (PadLot Bk Wl)) (ml : List (MsgLot Bk Wl))
    (wit : Wl → PlaceIn Xi) (own₀ : X) {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
    (rest : Nat → TreeLot Bk Wl) (T : Thread Bk S ProofFile.Cl V Wl X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = front)
    (htab : T.table =
      (Script.ofLots cF.blocksInOrder front cells tok pl (k1TreeLots wit own₀ jobs rest) ml).table)
    (hfix : T.fixed =
      (Script.ofLots cF.blocksInOrder front cells tok pl (k1TreeLots wit own₀ jobs rest) ml).fixed)
    (hnd : (jobs.map (·.1)).Nodup) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs)
    {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[x.1]? = some blk) :
    OwnTrees T x.1 (blk.oracles.flatMap id).length (treeTbl 0 wit x.2 own₀) (fun _ => 0) := by
  have e := ofLots_ownTrees cF.blocksInOrder front cells tok pl (k1TreeLots wit own₀ jobs rest) ml T hbs hfr
    htab hfix hblk
  rw [k1TreeLots_at wit own₀ rest hnd hx] at e
  exact e

/-- A fact: 3 is no number of the 52: there rest answers. -/
theorem rest_at_three (wit : Wl → PlaceIn Xi) (own₀ : X) (J₂ : SendJob (PlaceIn Xi) X)
    (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X) (Jw : SendJob (PlaceIn Xi) X)
    (rest : Nat → TreeLot Bk Wl) :
    k1TreeLots wit own₀ (k1MembersW J₂ Jl Jw) rest 3 = rest 3 := by
  refine k1TreeLots_rest wit own₀ rest ?_
  unfold k1MembersW k1Members
  rw [List.map_append, List.map_cons, List.map_flatMap]
  show 3 ∉ 2 :: (List.range 25).flatMap (fun l => [K1.noL l false, K1.noL l true]) ++ [356]
  decide +kernel

/-- **A NEGATIVE TEST: THE 52nd ENTRY IS READ**: over the 51 alone rest answers at 356; over the 52
W's own lot does. -/
theorem w_lot_bites (wit : Wl → PlaceIn Xi) (own₀ : X) (J₂ : SendJob (PlaceIn Xi) X)
    (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X) (Jw : SendJob (PlaceIn Xi) X)
    (rest : Nat → TreeLot Bk Wl) :
    k1TreeLots wit own₀ (k1Members J₂ Jl) rest 356 = rest 356 ∧
      k1TreeLots wit own₀ (k1MembersW J₂ Jl Jw) rest 356 = ⟨treeTbl 0 wit Jw own₀, fun _ => 0⟩ :=
  ⟨k1TreeLots_rest wit own₀ rest (w_not_in_51 J₂ Jl),
    k1TreeLots_at wit own₀ rest (k1MembersW_nodup J₂ Jl Jw)
      (x := (356, Jw)) (mem_k1MembersW.2 (Or.inr rfl))⟩

/-- **A NEGATIVE TEST: THE FIRST WINS, IN SILENCE**: at a list with one number twice the second
entry's number gets the first entry's lot. -/
theorem first_wins (wit : Wl → PlaceIn Xi) (own₀ : X) (J J' : SendJob (PlaceIn Xi) X)
    (rest : Nat → TreeLot Bk Wl) (b : Nat) :
    k1TreeLots wit own₀ [(b, J), (b, J')] rest ((b, J') : Nat × SendJob (PlaceIn Xi) X).1 =
      ⟨treeTbl 0 wit J own₀, fun _ => 0⟩ := by
  unfold k1TreeLots
  rw [List.lookup_cons_self]

/-- A table's first component is the job's own place: in both arms of treeTbl. A public value: the
same at all coins, in both arms. -/
theorem treeTbl_place {W : Type} (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (τ : Nat)
    (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) :
    (treeTbl ch wit J own₀ τ k w h).1 = J.P.place := by
  unfold treeTbl
  split <;> rfl

/-- **THE TOOTH: WITHOUT hnd k1TreeLots_at's END FAILS**: at two jobs whose plans' places part, at
one number: the second entry's number does NOT get the second entry's lot. k, w: any: only that
there are some: the two lots are told apart by their tables' first components there. -/
theorem first_wins_parts (wit : Wl → PlaceIn Xi) (own₀ : X) (J J' : SendJob (PlaceIn Xi) X)
    (rest : Nat → TreeLot Bk Wl) (b : Nat) (k : Coins Bk) (w : Wl)
    (hne : J.P.place ≠ J'.P.place) :
    k1TreeLots wit own₀ [(b, J), (b, J')] rest ((b, J') : Nat × SendJob (PlaceIn Xi) X).1 ≠
      ⟨treeTbl 0 wit J' own₀, fun _ => 0⟩ := by
  rw [first_wins]
  intro e
  have e1 := congrArg (fun L : TreeLot Bk Wl => (L.tbl 0 k w []).1) e
  dsimp only at e1
  rw [treeTbl_place, treeTbl_place] at e1
  exact hne e1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1TreeLots
#print axioms ProofFile.Honest.K1.k1TreeLots_at
#print axioms ProofFile.Honest.K1.k1TreeLots_rest
#print axioms ProofFile.Honest.K1.ownTrees_at_lots
#print axioms ProofFile.Honest.K1.rest_at_three
#print axioms ProofFile.Honest.K1.w_lot_bites
#print axioms ProofFile.Honest.K1.first_wins
#print axioms ProofFile.Honest.K1.treeTbl_place
#print axioms ProofFile.Honest.K1.first_wins_parts
