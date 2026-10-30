-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/OutAtRow.lean: THE OUTPUT HEAD'S OWN ROUNDS: UNDER 21
PREMISES, NAMED BELOW: AT THE ROUNDS THAT THE ROW PLAYS, THE MEMBER'S STEP ACCEPTS, AND BEHIND IT
K6Out HOLDS (Johnson/Desc/Kinds/Law/RowPins.lean) AT THE MASK ROW AND AT ALL CELLS c' WITH WHICH THE
PROVER'S AGREE INSIDE THE RANGES, WHICH MEET THE EQUATIONS, AND AT WHICH THE KEYS' SENTENCE HOLDS IN
FRONT (hHolds, hHonest, hK).
WHAT IT IS NOT. CONDITIONAL, ON MANY NAMED PREMISES, NONE OF WHICH IS SHOWN HERE OF ANY RUN; each
with who is meant to pay it:
  hg, keyTie THE VERIFIER'S LETTERS AT THE STATE ARE THOSE THAT THE PROVER'S SMALL INPUT MAKES, WORD
             FOR WORD: the lookups' border.
  hsame      the prover's cells and c' agree on what the head's relation names (Law/CellsAlike.lean:
             SameCells; the prover's first): whoever lays the witness and the reader of the trace.
  hHolds, hHonest   c' meets the equations: what is said of the segment's relation at c'.
  hroom      the ledger has room for the hearing's numbers: the promise in front.
  hzt        the lookup's point on the positions has lt coordinates: Hears/HalfPoint.lean. It
             follows from keyTie (the library's given_ok, then zt_of_points): Law/OutAtThread.lean
             derives it so; here it stays a premise. Neither of these two files is in the library.
  hd         the challenges are such as the declared rounds can sample.
  hfit, hbare   the played rounds pass the member's step's own test on rounds, and bear no digest:
             Plays.lean's k6_fits and k6_bare, conditional on K6Seated, which is not shown there of
             the IOP as written in Lean.
  hM         the mask row reads as the row's coins in the order of spending: Law/OutAtThread.lean's
             headSpent_eq ties headSpent to the frame's spentOf.
  hK         the keys' sentence holds in front, at c': the lookups' item, walked back.
  M, hk, hsm, hpl, hL, hfail, hopen, hstart, hgk   the member's form and the state in front (hgk: it
             holds what the lookup has heard), as Law/K6OutAtMember.lean's member_out takes them.
That the frame's play returns k6Out is Plays.lean's k6_played, not called here. c' AND THE MASK ROW
ARE LETTERS: that a law's reading of a witness (compCut) yields such is not said. Nothing on
soundness, on completeness or on what a proof hides; "no bad element is sampled" is neither asked
nor concluded. No example.
  words_of_fit       challenges that the declared rounds can sample are written canonically.
  canonical_outOf    rounds of moves that say scalars are written canonically, where the challenges
                     are.
  canon_append, canonical_piece, canonical_at_row   so are the row's played rounds.
  sameCells_refl     cells agree with themselves.
  truthK6N_at_row    THE ROUNDS THAT THE ROW PLAYS ARE AT THE TRUTH OF c': there are H and G with
                     TruthK6N. It takes three premises that the main statement does not: hreq, hy,
                     and hW: the ledger in front is well laid.
  out_at_row         THE MAIN STATEMENT. The test on the request and "the next token is below V" are
                     had of K6On and keyTie; the well-laid ledger of K6On.
  out_at_row_own     its instance at the prover's own cells.
A NAME: readsOf means the frame's own in this namespace: the library's is written Head.Law.readsOf.
PATHS. "Law/" above and below means Johnson/Desc/Kinds/Law/, but for Law/OutAtThread.lean, whose
place is beside this file; "Hears/" means Johnson/Desc/ProofFile/Honest/K6/Hears/; TablesSame.lean
and TruthAtState.lean lie in Johnson/Desc/K6/Honest/; Plays.lean and HidesAtRow.lean beside this
file.
CALLED: HidesAtRow.lean (hides_at_row), TablesSame.lean (HidesTables.same), Hears/Shaped.lean
(hears_shaped), Law/K06FitsShape.lean (shapedNZ_of_blockFit), TruthAtState.lean
(truthK6N_of_hides), Law/K6OutAtMember.lean (member_out, K6MemberIs.on), Law/K6WayUp.lean
(K6MemberIs.rounds), Plays.lean (k6Out_eight, k6Coin_0 .. k6Coin_7, k6Piece_at); drawsFit_length
(Honest/Law/Along.lean); of the library: okE_ofK, given_ok.
-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Law.HidesAtRow
import Johnson.Desc.ProofFile.Honest.K6.Hears.Shaped
import Johnson.Desc.K6.Honest.TruthAtState
import Johnson.Desc.K6.Honest.TablesSame
import Johnson.Desc.Kinds.Law.K6OutAtMember
import Johnson.Desc.Kinds.Law.K06FitsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes (E)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Head.Par Head.Given Head.HeardAll Head.Law.readsOf
  FinalNorm.zt Norm.lt Norm.lPd)
open VerifiableInference.Desc.Kinds.Head (parOf given seatAt blockAt startOk)
open VerifiableInference.Desc.Kinds.Head.Law (Canonical WellLaid Fresh workOf dataOf
  HonestHead KeysWorth K6Out K6Left K6MemberIs HeadOpen TruthK6N truthK6N_of_hides
  shapedNZ_of_blockFit member_out okE_ofK NCells SameCells)
open SumLaw (outOf rvSaid)

variable {W' X' : Type}

/-! ## 1 Canonical writing -/

/-- Challenges that the declared rounds can sample are written canonically. -/
theorem words_of_fit : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit zs ds = true →
    ∀ d ∈ ds, ∀ x ∈ d.elems, OnBytes.okE (E.ofTriple x) = true
  | [], [], _ => fun _ hd => absurd hd List.not_mem_nil
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | _ :: zs, _ :: ds, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    intro d hd x hx
    rcases List.mem_cons.1 hd with rfl | hd'
    · have h1 := h.1
      simp only [drawFit, Bool.and_eq_true] at h1
      exact List.all_eq_true.1 h1.1.2 x hx
    · exact words_of_fit zs ds h.2 d hd' x hx

/-- Rounds of moves that say scalars are written canonically, where the challenges are. -/
theorem canonical_outOf : ∀ (gs : List (Seen → State W' X' → List E)) (t : State W' X')
    (seen : Seen) (ds : List Fmt.Drawn),
    (∀ d ∈ ds, ∀ x ∈ d.elems, OnBytes.okE (E.ofTriple x) = true) →
    Canonical (outOf gs t seen ds)
  | g :: gs, t, seen, d :: ds, h => by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr'
    · refine ⟨fun x hx => ?_, fun x hx => h d List.mem_cons_self x hx⟩
      have e : (rvSaid (g seen t) d).vals = (g seen t).map fun y =>
          Fmt.ItemValue.e (OnBytes.Slice.ofE (OnBytes.Slice.toE y.triple)) := by
        show ((g seen t).map _).map _ = _
        rw [List.map_map]
        rfl
      rw [e] at hx
      obtain ⟨y, _, hy⟩ := List.mem_map.1 hx
      obtain rfl : OnBytes.Slice.ofE (OnBytes.Slice.toE y.triple) = x := by injection hy
      exact okE_ofK _
    · exact canonical_outOf gs _ _ ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) r hr'
  | [], _, _, [], _ => fun _ hr => absurd hr List.not_mem_nil
  | [], _, _, _ :: _, _ => fun _ hr => absurd hr List.not_mem_nil
  | _ :: _, _, _, [], _ => fun _ hr => absurd hr List.not_mem_nil

theorem canon_append {a b : List Fmt.RoundView} (ha : Canonical a) (hb : Canonical b) :
    Canonical (a ++ b) := fun r hr => (List.mem_append.1 hr).elim (ha r) (hb r)

section Row
variable {W₀ Rc Tr X : Type}

/-- A piece of the row's played rounds is written canonically, where the challenges are. -/
theorem canonical_piece (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) (i : Nat)
    (x : (s : ProofFile.Honest.Small.Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x)
    (hw : ∀ d ∈ ds, ∀ x ∈ d.elems, OnBytes.okE (E.ofTriple x) = true) :
    Canonical (k6Piece wit p at_ c t seen ds i) := by
  rw [k6Piece_at wit p at_ c t seen ds i x h]
  exact canonical_outOf _ _ _ _ fun d hd =>
    hw d (List.mem_of_mem_drop (List.mem_of_mem_take hd))

/-- **The row's played rounds are written canonically**, at challenges that the declared rounds can
sample. -/
theorem canonical_at_row (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) (nm : String)
    (hd : drawsFit p.rounds ds = true) :
    Canonical (roundsOf (k6Out nm wit p at_ c t seen ds)) := by
  have hw := words_of_fit _ _ hd
  rw [k6Out_eight]
  exact canon_append (canonical_piece wit p at_ c t seen ds 0 _ (k6Coin_0 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 1 _ (k6Coin_1 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 2 _ (k6Coin_2 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 3 _ (k6Coin_3 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 4 _ (k6Coin_4 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 5 _ (k6Coin_5 wit p at_ c) hw)
    (canon_append (canonical_piece wit p at_ c t seen ds 6 _ (k6Coin_6 wit p at_ c) hw)
      (canonical_piece wit p at_ c t seen ds 7 _ (k6Coin_7 wit p at_ c) hw)))))))

/-! ## 2 At the state -/

/-- Cells agree with themselves. -/
theorem sameCells_refl [VerifiableInference.Desc.Kinds.Head.Sizes]
    [VerifiableInference.Desc.Kinds.Head.Policy] [VerifiableInference.Desc.Kinds.Head.Request]
    [VerifiableInference.Desc.Kinds.Head.Token] (c : NCells) : SameCells c c :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

/-- **THE ROUNDS THAT THE ROW PLAYS ARE AT THE TRUTH OF ALL CELLS c' WITH WHICH THE PROVER'S AGREE**
on what the head's relation names, at the verifier's state s in front of the member. g: the letters.
m: how many free numbers are left behind the hearing. The equations on the cells are asked at c'.
The ledger in front is asked to be well laid (hW). -/
theorem truthK6N_at_row [g : Head.Given] (W : OnBytes.Model.Verify.Public) (l : Nat)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit (parOf W.hS (workOf W)) at_))
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (ds : List Fmt.Drawn) (nm : String)
    (s : S) (mask : Nat → E) (m : Nat) (c' : NCells)
    (hg : g = (wit t.input).given (parOf W.hS (workOf W)) t.heard)
    (keyTie : given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s = .ok g)
    (hsame : SameCells (wit t.input).cells c')
    (hreq : VerifiableInference.Desc.Kinds.Head.Request.ok = true)
    (hy : VerifiableInference.Desc.Kinds.Head.y < VerifiableInference.Desc.Kinds.Head.V)
    (hHolds : (dataOf c').Holds) (hHonest : HonestHead c'.toCells)
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s))
    (hroom : Fresh ((seatAt W.hS (Head.Law.readsOf W)).ledger s)
      (41 + 8 * Norm.lt + 4 * Norm.lPd + m))
    (hzt : (FinalNorm.zt).size = Norm.lt)
    (hd : drawsFit (parOf W.hS (workOf W)).rounds ds = true)
    (hfit : roundsFit (blockAt W.hS (Head.Law.readsOf W) (workOf W) l).rounds
      (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) = true)
    (hbare : (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)).map noDigest =
      roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds))
    (hM : headTiedFrom mask ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (headSpent (p := (parOf W.hS (workOf W))) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1)) :
    ∃ (H : Head.HeardAll) (G : Fork), TruthK6N W.hS (Head.Law.readsOf W) (workOf W) s
      c' mask (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) H G := by
  have hsh := shapedNZ_of_blockFit W.hS (Head.Law.readsOf W) (workOf W) l _ hfit
  rw [hbare] at hsh
  have hsh' : VerifiableInference.Desc.Kinds.Head.Law.ShapedNZ
      (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds))
      VerifiableInference.Desc.Kinds.Head.rounds := by
    subst hg
    exact hsh
  obtain ⟨H, G, hh, _, _, _, _, sPV, sS, sP, sN, sL⟩ :=
    Hears.hears_shaped hW hroom hzt _ hsh'
  exact ⟨H, G, truthK6N_of_hides W.hS (Head.Law.readsOf W) (workOf W) s _ mask _ H G g keyTie hHolds
    hHonest
    (canonical_at_row wit _ at_ c t seen ds nm hd) hsh' hh sPV sS sP sN sL hzt
    (VerifiableInference.Desc.Kinds.Head.Honest.HidesTables.same hsame hreq hy sPV sP sN sL hzt
      (hides_at_row wit _ at_ c t seen ds nm hg (drawsFit_length _ _ hd) _ G H mask hW hh hzt hM))⟩

/-- **CONDITIONAL, ON 21 PREMISES: AT THE ROUNDS THAT THE ROW PLAYS THE MEMBER'S STEP ACCEPTS, AND
BEHIND IT K6Out HOLDS** at all cells c' with which the prover's agree on what the head's relation
names, and the mask row. The equations on the cells and the keys' sentence are asked at c'. H, G
stand under "there is": the end says of them only that s' has the ledger G and has H laid as heard;
in the proof they are the hearing's own return, and no clause of the statement says so. The load of
the end is the step's return and K6Out, which reads the ledger and what was heard off s' itself;
truthK6N_at_row hands out "there are H and G with TruthK6N" beside.
hg and keyTie are one sentence in two, for the class's sake: the verifier's given at s returns the
prover's letters. Two places stand here, the member's a and the row's at_, which only the names of
the coins' runs bear: nothing ties them, and at_ reaches no value. -/
theorem out_at_row [g : Head.Given] {W : OnBytes.Model.Verify.Public} {l : Nat}
    {same : S → S → Bool} {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b)
    (hk : a.kind ≠ KindName.K7) (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true)
    (hpl : b.planOk = true) (ft : Nat) (cols : List OpenedColumn)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit (parOf W.hS (workOf W)) at_))
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (ds : List Fmt.Drawn) (nm : String)
    (s : S) (mask : Nat → E) (m : Nat) (c' : NCells) (hL : K6Left W s) (hfail : s.failed = none)
    (hopen : HeadOpen s) (hstart : startOk W s = true)
    (hg : g = (wit t.input).given (parOf W.hS (workOf W)) t.heard)
    (keyTie : given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s = .ok g)
    (hsame : SameCells (wit t.input).cells c') (hHolds : (dataOf c').Holds)
    (hHonest : HonestHead c'.toCells)
    (hroom : Fresh ((seatAt W.hS (Head.Law.readsOf W)).ledger s)
      (41 + 8 * Norm.lt + 4 * Norm.lPd + m))
    (hzt : (FinalNorm.zt).size = Norm.lt)
    (hd : drawsFit (parOf W.hS (workOf W)).rounds ds = true)
    (hfit : roundsFit b.rounds (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) =
      true)
    (hbare : (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)).map noDigest =
      roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds))
    (hM : headTiedFrom mask ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (headSpent (p := (parOf W.hS (workOf W))) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1))
    (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk)
    (hK : KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s c' mask gk) :
    ∃ (s' : S) (H : Head.HeardAll) (G : Fork),
      b.step ft s (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) cols =
        .ok (s', 0) ∧
      (seatAt W.hS (Head.Law.readsOf W)).ledger s' = G ∧
      (seatAt W.hS (Head.Law.readsOf W)).heard s' = some H ∧
      K6Out W s' (c', mask) := by
  obtain ⟨a1, _, _, a4, a5, _⟩ := M.on hpl hstart hL
  have hreq : VerifiableInference.Desc.Kinds.Head.Request.ok = true := by
    obtain ⟨_, _, _, _, _, e⟩ :=
      VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g keyTie
    subst e
    exact a4
  have hy : VerifiableInference.Desc.Kinds.Head.y < VerifiableInference.Desc.Kinds.Head.V := by
    obtain ⟨_, y0, _, hy0, _, e⟩ :=
      VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g keyTie
    subst e
    exact a5 y0 hy0
  obtain ⟨H, G, R⟩ := truthK6N_at_row W l wit at_ c t seen ds nm s mask m c' hg keyTie hsame hreq hy
    hHolds hHonest a1 hroom hzt hd (by rw [← M.rounds]; exact hfit) hbare hM
  obtain ⟨s', hst, bL, bH, hO⟩ := member_out M hk hsm hpl ft cols s _ mask _ H G hL hfail hopen
    hstart R gk hgk hK
  exact ⟨s', H, G, hst, bL, bH, hO⟩

/-- **THE SAME AT THE PROVER'S OWN CELLS**: the instance c' := the prover's cells. CONDITIONAL as
out_at_row is; of H and G the same holds as there. -/
theorem out_at_row_own [g : Head.Given] {W : OnBytes.Model.Verify.Public} {l : Nat}
    {same : S → S → Bool} {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b)
    (hk : a.kind ≠ KindName.K7) (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true)
    (hpl : b.planOk = true) (ft : Nat) (cols : List OpenedColumn)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit (parOf W.hS (workOf W)) at_))
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (ds : List Fmt.Drawn) (nm : String)
    (s : S) (mask : Nat → E) (m : Nat) (hL : K6Left W s) (hfail : s.failed = none)
    (hopen : HeadOpen s) (hstart : startOk W s = true)
    (hg : g = (wit t.input).given (parOf W.hS (workOf W)) t.heard)
    (keyTie : given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s = .ok g)
    (hHolds : (dataOf (wit t.input).cells).Holds)
    (hHonest : HonestHead (wit t.input).cells.toCells)
    (hroom : Fresh ((seatAt W.hS (Head.Law.readsOf W)).ledger s)
      (41 + 8 * Norm.lt + 4 * Norm.lPd + m))
    (hzt : (FinalNorm.zt).size = Norm.lt)
    (hd : drawsFit (parOf W.hS (workOf W)).rounds ds = true)
    (hfit : roundsFit b.rounds (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) =
      true)
    (hbare : (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)).map noDigest =
      roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds))
    (hM : headTiedFrom mask ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (headSpent (p := (parOf W.hS (workOf W))) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1))
    (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk)
    (hK : KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s
      (wit t.input).cells mask gk) :
    ∃ (s' : S) (H : Head.HeardAll) (G : Fork),
      b.step ft s (roundsOf (k6Out nm wit (parOf W.hS (workOf W)) at_ c t seen ds)) cols =
        .ok (s', 0) ∧
      (seatAt W.hS (Head.Law.readsOf W)).ledger s' = G ∧
      (seatAt W.hS (Head.Law.readsOf W)).heard s' = some H ∧
      K6Out W s' ((wit t.input).cells, mask) :=
  out_at_row M hk hsm hpl ft cols wit at_ c t seen ds nm s mask m _ hL hfail hopen hstart hg keyTie
    (sameCells_refl _) hHolds hHonest hroom hzt hd hfit hbare hM gk hgk hK

end Row

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.words_of_fit
#print axioms ProofFile.Honest.K6.canonical_outOf
#print axioms ProofFile.Honest.K6.canon_append
#print axioms ProofFile.Honest.K6.canonical_piece
#print axioms ProofFile.Honest.K6.canonical_at_row
#print axioms ProofFile.Honest.K6.sameCells_refl
#print axioms ProofFile.Honest.K6.truthK6N_at_row
#print axioms ProofFile.Honest.K6.out_at_row
#print axioms ProofFile.Honest.K6.out_at_row_own
