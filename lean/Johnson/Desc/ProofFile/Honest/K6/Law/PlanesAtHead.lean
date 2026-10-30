-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/PlanesAtHead.lean.
WHAT IT IS NOT. IT STANDS OVER A FILE OF OTHER AUTHORS THAT IS A READING COPY AND HAS NOT BEEN
HANDED IN (Honest/K3/Law/Total/PlanesAt341MgAll.lean: the law on the item "planes", without a
thread). THE SHARE IS CONDITIONAL ON THE LIBRARY's HYPOTHESIS P5J.AtMgA AND ON ONE NAMED PREMISE,
SHOWN HERE OF NOTHING: hIn: at every valid input the prover's cells are in range. THAT THE ITEM
worth 24 3 "planes" HOLDS IN FRONT IS READ OFF THE THREAD's SENTENCE AT BORDER 341: it is owed by
the row in front (the lookup on the calls): WHOEVER SHOWS THAT THE THREAD HOLDS THERE PAYS IT, AT
THE COMPOSED MEANING's OWN READING OF THE CALLS: nothing here does. That the thread holds at any run
is shown nowhere. ExchangeAtS and ExchangeS are definitions (Honest/Thread/SharesS.lean,
PaysS.lean): premises' forms: none of the library's goals. That the verifier accepts is the debt's
own premise: nothing here shows it. THE DEBT ExchangeS IS NOT SHOWN: beside the hypothesis the last
statement stands under three premises (hIn, K6HalfAt, K6Script), the last but one under five (these,
hKp', BehindS), the third under five (hKp', K6HalfAt, K6Script, BehindS, hPlanes), each shown here
of nothing; THE CONTENT ON VALUES LIES IN K6Script, IN hIn AND IN WHAT THE THREAD's SENTENCE HOLDS
OPEN IN FRONT. A JOIN: NO NEW MATHEMATICS. (Of the hypothesis the library has a member under four
premises on the three public files: P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean;
nothing here calls that.) The full size, the format's second hash function, border 341 and segment 24 alone.
Nothing on soundness, on completeness or on what a proof hides.
WHAT IT IS. THE SUB-PROTOCOL "the output head's own rounds": ITS SHARE OF THE DEBT ExchangeS AT THE
ITEM formsT 24 3 "planes", AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS (lettersHead,
Honest/Thread/FirstHead.lean), at every letter Said and every letter Kp; and that debt with all
seven shares of the row laid in, at last at every letter Kp too.
  k6_exchange_planes            THE SHARE
  k6_exchange_at_head'          the shares at "own", "join", "weights": k6_exchange_at_head_keeps
                                without hKp
  k6_exchangeS_at_head'         k6_exchangeS_at_head without hKp
  k6_exchangeS_at_head_planes   the debt ExchangeS at border 341 with the share at "planes" laid in:
                                hIn in hPlanes' stead
  k6_exchangeS_at_head_free     THE SAME WITHOUT hKp' AND hB: under the hypothesis, hIn, K6HalfAt
                                and K6Script alone
ON THE LETTER Kp. Honest/K6/Law/ShareAtHead.lean's k6_exchange_at_head_keeps and
ExchangeAtHead.lean's k6_exchangeS_at_head ask hKp (K6Keeps s s' → Kp plK6 s s'). IT IS IDLE THERE
IN SUBSTANCE: it is handed down to k6_form_keeps (Honest/K6/Law/Behind.lean), of whose end these
keep the first half alone, and that half's proof does not spend it. The two statements with a prime
here are these two without it. The converse hKp' and the debt BehindS (hB) are spent in the text of
k6_exchangeS_of_four (Honest/K6/Law/RidesPast.lean), for the shares at pin 24 0 and constr 24 small,
AND ARE IDLE THERE IN SUBSTANCE TOO: Honest/K6/Law/RidesAtStep.lean says why, and has these shares
without them: so the last statement here.
WHO PAYS WHAT. The law: planes_field_mgAll (Honest/K3/Law/Total/PlanesAt341MgAll.lean): twenty-one
premises. The item in front (hw), the test behind (hin), the decision, K6On and the nine premises on
the two states, the three public facts, and what the item means: Honest/K6/Law/PlanesFront.lean. The
caller's two equations and the shape's test: meets_at_head, calls_at_head
(Honest/K6/Law/LettersAtHead.lean). The table's public item "left" in front: K6FrontItems.left at
headFrontItems_of_thr (Honest/K6/Law/FrontAt.lean). The bare sub-protocol is there: K6MemberIs.bare
at k6_member_at_mg (Johnson/Desc/Kinds/Law/K6WayUp.lean, K6WayUpAtSeat.lean). The run under the
name: the library's runs_at_head. In range: hIn, at the thread's clause that the input is valid. One
list of challenges in front and behind: play_mid (Honest/Law/Along.lean), play_heard
(Honest/Thread/PaysLaw.lean), as in exchangeAtS_again (Honest/Thread/SharesS.lean). The two with a
prime: k6_exchange_at_head at k6_forms_behindS' (Honest/K6/Law/FormBehind.lean);
k6_exchangeS_of_four (Honest/K6/Law/RidesPast.lean). The last: k6_exchangeS_of_four'
(Honest/K6/Law/RidesAtStep.lean).
OF THE FOLDER Johnson/Goal/ it imports no module by name.
It imports, beside library files, those named above under Honest/ and what they import.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.PlanesFront
import Johnson.Desc.ProofFile.Honest.K6.Law.ExchangeAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.RidesAtStep
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.PlanesAt341MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Place Strs noDigest)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6)
open VerifiableInference.OnPublicFiles.Flat (InRange)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (Thread BehindS ExchangeS ExchangeAtS ProverCoinCounts Coins Local Mid Prover play_mid
  play_heard)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (HeadAsk K6Script K6HalfAt headFrontItems_of_thr k6_forms_behindS'
  k6_exchangeS_of_four k6_exchangeS_of_four')
open ProofFile.Honest.K3.Law.Total (planes_field_mgAll)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **THE SHARE OF ExchangeS AT THE ITEM formsT 24 3 "planes", AT THE LIBRARY's OWN LETTERS**, at
every letter Said and every letter Kp. CONDITIONAL on the hypothesis that ties the table's letters
to the IOP as written in Lean; on hIn: at every valid input (the letter w, where Vd holds of it) the
prover's cells are in range. The item worth 24 3 "planes" in front is read off the thread's
sentence. -/
theorem k6_exchange_planes (hIn : ∀ v, (v = w ∧ Vd v) → InRange (Q.cells v)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.formsT 24 3 "planes") := by
  intro blk hblk k s m E ds y cl s' hA hd hS ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  obtain ⟨b, -, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hv : m.st.input = w ∧ Vd m.st.input := hA.1.2.2.2.2.2.2
  obtain ⟨gs, hbel, hOn, aK, cU, Pd⟩ :=
    k6_planesDue_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lk hlk m.st.input blk hblk k s
      m E ds y cl s' hA.1 hd hS
  have hw := k6_planes_worth_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA.1 (ds ++ ds')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1))
  have hin := k6_planes_in_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y
    cl s' hA.1 hd hS
  obtain ⟨-, R⟩ := headFrontItems_of_thr
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hA.1
  obtain ⟨-, hlm, -⟩ := plane_at_head h
  have hRange : InRange ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k
      m.st.input (m.st.heard ++ (ds ++ ds'))).cells := by
    show InRange (Q.cells m.st.input)
    exact hIn _ hv
  have key := planes_field_mgAll (D := dofAtHead h Q carryX m.st.input) mgBase
    (meets_at_head h (fun _ _ => some (Q.cells m.st.input)) carryX).fits hlm
    (((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s).1, s)
    (((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k y.2 s').1, s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1))
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
      (m.st.heard ++ (ds ++ ds'))) _ M.bare ((ProofFile.Honest.roundsOf y.1).map noDigest) gs hbel
    hOn (K9.statesOfLink Lk)
    (P4.six_of_link_at_head h hlk).2.2.1 Pd.rd hin aK Pd.seg Pd.ns cU Pd.arr Pd.stated Pd.wide
    Pd.len Pd.shape (calls_at_head h).2.1 (Pd.nu _) hRange hw R.left
    (runs_at_head (dofAtHead h Q carryX m.st.input) A.sorts).2.1
  show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means y.2.st.input
    (Item.formsT 24 3 "planes")
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k y.2 s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1))
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k y.2.st.input
      (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc]
  exact k6_means_planes h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ _ key

/-- **THE SHARES AT "own", "join", "weights"**: `k6_exchange_at_head_keeps` without hKp: at every
letter Kp. CONDITIONAL on the hypothesis and on the two named premises on the prover's halves and on
what ties the prover's cells, coins and letters to what the law reads off the witness. -/
theorem k6_exchange_at_head' (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "own") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "join") ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (Item.formsT 24 4 "weights") :=
  k6_exchange_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH Said Hc
    (k6_forms_behindS' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said)

/-- **`k6_exchangeS_at_head` without hKp.** CONDITIONAL on the hypothesis; on hPlanes: the share at
"planes"; on hB: the debt BehindS at the border; on hKp': at the sub-protocol's place the letter Kp
gives the sub-protocol's own clause of what its step keeps; and on the two named premises. THE DEBT
IS NOT SHOWN. -/
theorem k6_exchangeS_at_head' (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s')
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX))
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (hPlanes : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 3 "planes")) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  obtain ⟨hOwn, hJoin, hWeights⟩ :=
    k6_exchange_at_head' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said wit hH Hc
  exact k6_exchangeS_of_four h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB hKp' hOwn hPlanes
    hJoin hWeights

/-- **THE DEBT ExchangeS AT THE OUTPUT HEAD's OWN ROUNDS, WITH ALL SEVEN SHARES LAID IN**, at every
letter Said. CONDITIONAL on the hypothesis; on hIn; on hB: the debt BehindS at the border; on hKp';
and on the two named premises on the prover's halves and on what ties the prover's cells, coins and
letters to what the law reads off the witness. THE DEBT IS NOT SHOWN. -/
theorem k6_exchangeS_at_head_planes (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s')
    (hIn : ∀ v, (v = w ∧ Vd v) → InRange (Q.cells v))
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX))
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 :=
  k6_exchangeS_at_head' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hKp' wit hH Hc hB
    (k6_exchange_planes h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hIn)

/-- **THE DEBT ExchangeS AT THE OUTPUT HEAD's OWN ROUNDS, AT EVERY LETTER Kp AND WITHOUT THE DEBT
BehindS**, at every letter Said: `k6_exchangeS_at_head_planes` without hKp' and hB, which are idle
there in substance. CONDITIONAL on the hypothesis; on hIn; and on the two named premises on the
prover's halves and on what ties the prover's cells, coins and letters to what the law reads off the
witness. THE DEBT IS NOT SHOWN. -/
theorem k6_exchangeS_at_head_free (hIn : ∀ v, (v = w ∧ Vd v) → InRange (Q.cells v))
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX)) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  obtain ⟨hOwn, hJoin, hWeights⟩ :=
    k6_exchange_at_head' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said wit hH Hc
  exact k6_exchangeS_of_four' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hOwn
    (k6_exchange_planes h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hIn) hJoin hWeights

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchange_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchange_at_head'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_at_head'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_at_head_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_at_head_free
