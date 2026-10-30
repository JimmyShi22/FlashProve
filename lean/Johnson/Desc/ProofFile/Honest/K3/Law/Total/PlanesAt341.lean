-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/PlanesAt341.lean: the kind "lookup" (K3). Conditional:
the library's way from the item formsT of the table of borders, at the run "planes" of the lookup on
the head's calls, to the sentence at worth "planes" (Johnson/Desc/Kinds/Law/PlanesRoad.lean,
Johnson/Desc/Kinds/Law/PlanesArm.lean), gone the other way: from the sentence at worth "planes" in
front of the head's own sub-protocol, the public test formsInT behind its acceptance, and what the
lookup left, to the item formsT behind it. At letters. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table of borders is Johnson/Desc/First/Borders.lean,
whose head calls it the table of joints. The item formsT at a run is `Sound.formsTQ`
(Johnson/Desc/Sound/FormsQ.lean); its public test is `K9.formsInT`. The sentence at worth "planes"
is `K3OutPlanes` (Johnson/Top/H/K3RowOut.lean): the library's three claims on the planes are 0. What
the lookup on the calls left is `K3LeftAt` (Johnson/Top/H/K3LeftStatement.lean), or in the form of
the table's public item "left" `k3LeftItemAt` (Johnson/Desc/First/Look/K3LeftItem.lean).

What is shown.
  `forms_of_outPlanes`: the library's `outPlanes_of_forms` (PlanesRoad.lean) with its hypothesis on
    the forms and its conclusion exchanged; besides it assumes the public test and one list of
    rounds.
  `planes_arm_back`: the library's `planes_arm` (PlanesArm.lean) the other way: s is the state in
    front of the head's own sub-protocol, t the state behind its acceptance; the list of rounds
    comes out of `K3LeftAt` at s.
  `planes_arm_back_item`: the same with that hypothesis in the form of the table's own public item.
The statements speak of no thread, prover or coin.

Hypotheses that remain. None of them is shown in this file.
  new here: `hin`, the public test formsInT behind; the list of rounds (in `forms_of_outPlanes`:
    `hk`, `hI`, `hL0`: what the lookup heard stands for that list from the ledger F0, and the open
    ledger is later than F0 and has its sizes), or what the lookup left at s (`hL`); `hw` (named
    `hOut` in `forms_of_outPlanes`), the sentence at worth "planes"; in `planes_arm_back_item` three
    equations on the item's place (`hp`): its shape, its packing and its first slot are the
    letters'.
  those of the library's two theorems, name for name: `hSt`, `PlanesStates` (PlanesRoad.lean);
    `hRd`, the reader at (b, "planes") is the filling `k6Silent`
    (Johnson/Desc/Kinds/Law/K6SilentCode.lean); `hmask`, the reading has the stated data's mask row;
    the stated cells of the reads' array (`ha`, `hArr`, `hcell`); two inequalities on widths
    (`hwide`, `hlen`); in `forms_of_outPlanes`, in the stead of these five, `hHost`
    (`K3HostPlanes`), which `planes_arm_back` draws from them; the shape (`hsh`, `hok`); `hb`, `h`:
    blk is the link's sub-protocol, and the decision of `Sound.below blk` (blk with the test on the
    words in front) accepts from s to t; `hOn`, `K6On`
    (Johnson/Desc/Kinds/Law/RowPins.lean) in front. They are the calling kind's, as the library's
    own heads say of them.

Imported. Two files of the library.
By a program's count, no module under Johnson/Goal/ stands in their import closures; no
name of that folder is called.

How the proof goes. Why the way can be gone back: the library's proof has five steps, and one alone
has a direction. The reader's answer gives the run's acceptance, its two ledgers, its forms and late
slots (`reader_planes`, PlanesRoad.lean). At that acceptance the three forms' values are the
library's three claims at the values of the calling kind's readers' forms: an equation of lists
(`planes_worth`, Johnson/Top/H/K3RunsLaw.lean). A form's value in the world of the forms is its
value in the world of the ledger behind the run (`Sound.value_eq`, FormsQ.lean; slot by slot by
`slot_late`, PlanesRoad.lean). The values of the readers' forms are the columns under the reading
(`K3HostPlanes`, Johnson/Meaning/PlanesLaw.lean). These are three congruences. The step with a
direction is "the values are 0".
What the way back must bring that the forward way gets for nothing: a list of rounds for which what
the lookup heard stands. The sentence at worth "planes" says: at every such list the three claims
are 0; without one it says nothing. One lies in the table's public item "left", at the front state's
own ledger.

Users. `planes_back_mgAll` (Honest/K3/Law/Total/PlanesAt341MgAll.lean) calls `planes_arm_back_item`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At no state have the hypotheses been shown to hold together. The head's link alone: the like at the
calling kind of a layers' or an attention link is not looked at.
At which reading is the sentence at worth "planes" had? The hypothesis `hw` asks it at the reading
nuL t (…), the calling kind's letter. `outPlanes_of_left`
(Honest/K3/Law/Thread/ExchangePlanes.lean), which shows that sentence on the honest side, ends in it
at a reading under whose mask entries lie the coins that the stages take under the lookup's slots
(`Dict`), and whose cells are the data's bits. No statement of this file says that the calling
kind's reading is such a one.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Kinds.Law.PlanesArm
import Johnson.Desc.First.Look.K3LeftItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Total
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff World Reading)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Readers segAt? RunOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn slotW)
open VerifiableInference.OnPublicFiles

/-- **The planes' way, the other way.** Here s is the verifier's state behind the head's own
sub-protocol. Conditional on the hypotheses of the library's `outPlanes_of_forms` but for the
item; on the public test formsInT at the run "planes"; on one list of rounds for which what the
lookup heard stands from the ledger F0; and on the library's three claims on the planes being 0 at
every such list. Then the item formsT at the run "planes" holds at s of the witness's tables rdW.
No instance of these hypotheses is exhibited in this file. -/
theorem forms_of_outPlanes (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (lm b : Nat)
    (states : Nat → List (RunOf S)) (hSt : PlanesStates (readsOf W) lm states b) (Rd : Readers)
    (St : Sound.Stated) (own : List (Nat × Nat)) (s : S) (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms b "planes" s = k6Silent P states b "planes" s)
    (hin : K9.formsInT Rd own b "planes" s = true) (nu : _root_.Fo.Pl → K)
    (hmask : ∀ a, segAt? s = some a → ∀ j, j < a.F.ns →
      (St.at1 s (Sound.dataQ own a rdW)).mask j = nu (.mask j))
    (hHost : ∀ e a r gk (Wd : World K), withTables P s = some e → segAt? s = some a →
      callerReaders (planesAt (readsOf W)) e = some r → e.lookHeard? = some gk →
      Wd.entry = (worldOwn a [] (St.at1 s (Sound.dataQ own a rdW))).entry →
      Meaning.Planes.K3HostPlanes gk.shape lm (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) nu (fun f => f.value Reading.gl Wd)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}))
    (gk : OnBytes.Model.Forest.Heard) (hk : s.lookHeard? = some gk)
    (hok : FoNums.ok gk.shape = true) (F0 : Fork) (first : Nat)
    (hL0 : ∀ F, s.fork? = some F → _root_.Fo.Later F0 F ∧ OnBytes.PscRun.Sized F)
    (rs : TwV.Rounds K)
    (hI : _root_.Fo.HeardIs Reading.gl gk F0 (_root_.Fo.endsOf gk.shape lm first rs))
    (hOut : K3OutPlanes gk.shape lm first nu Reading.gl gk F0) :
    Sound.formsTQ Rd St own b "planes" s rdW := by
  have hin0 := hin
  unfold K9.formsInT at hin0
  cases ha : segAt? s with
  | none =>
    rw [ha] at hin0
    exact absurd hin0 (by simp)
  | some a =>
    cases hR : Rd.forms b "planes" s with
    | none =>
      rw [ha, hR] at hin0
      exact absurd hin0 (by simp)
    | some R =>
      rw [ha, hR] at hin0
      obtain ⟨hl, hall0⟩ := Eq.mp (Bool.and_eq_true _ _) hin0
      have hall := List.all_eq_true.1 hall0
      refine ⟨a, R, ha, hR, hl, fun f hf => ⟨hall f hf, ?_⟩⟩
      have hR' := hR
      rw [hRd] at hR'
      unfold k6Silent at hR'
      obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.1 hR'
      obtain ⟨z, F, G, hrun, hF, hG, hforms, hlate⟩ := reader_planes hSt hRe
      obtain ⟨a', tt, ha', hee⟩ := withTables_spec he
      have hFs : s.fork? = some F := by
        rw [← hF, hee]
        unfold S.fork?
        rw [ha']
      have hks : e.lookHeard? = some gk := by
        rw [← hk, hee]
        unfold S.lookHeard?
        rw [ha']
      obtain rfl : a.F = F := Option.some.inj ((seg_fork ha).symm.trans hFs)
      obtain ⟨hLF, hSF⟩ := hL0 _ hFs
      obtain ⟨gk', r, hk', hr, _⟩ := planesRun_at asClaim W lm 0 e z hrun
      obtain rfl : gk' = gk := Option.some.inj (hk'.symm.trans hks)
      obtain ⟨G', hG', _, hLG, _, _, hv⟩ := planes_worth (K3.seatCalls asClaim) (·.form)
        (seatCalls_fits asClaim (·.form) fun _ => rfl) lm (callerReaders (planesAt (readsOf W))) K
        Reading.gl gk' first rs F0 a.F 0 e z.2 z.1 hks hF hI hLF hok hSF hrun
      obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
      have hv' := hv G' (_root_.Fo.Later.refl _) nu
        (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry
      have H := hHost e a r gk' (G'.worldOf Reading.gl (fun j => nu (.mask j))
        (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry) he ha hr hks rfl
      obtain ⟨k1, k2, k3⟩ := hOut rs hI
      have e0 : _root_.Fo.rdL Reading.gl gk'.zb0 =
          (_root_.Fo.endsOf gk'.shape lm first rs).zb0 := hI.zb0
      have e1 : _root_.Fo.rdL Reading.gl gk'.zb1 =
          (_root_.Fo.endsOf gk'.shape lm first rs).zb1 := hI.zb1
      have hb : ∀ q col, bitOf (callerReaders (planesAt (readsOf W))) e q col =
          (r.1 q col).getD {} := by
        intro q col
        unfold bitOf
        rw [hr]
        rfl
      have hp : ∀ col, pinOf (callerReaders (planesAt (readsOf W))) e col =
          (r.2 col).getD {} := by
        intro col
        unfold pinOf
        rw [hr]
        rfl
      have hz : ∀ x ∈ z.1.map (fun c => c.form.value Reading.gl
          (G'.worldOf Reading.gl (fun j => nu (.mask j))
            (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry)), x = 0 := by
        rw [hv']
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [claimLeaves_congr gk'.shape lm first rs nu _
            (_root_.Fo.colsK gk'.shape lm (_root_.Fo.rdL Reading.gl gk'.zb0) nu) (fun col hc => by
              rw [hb]
              exact H.bit0 col hc), e0]
          exact k1
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [claimBits_congr gk'.shape lm first rs nu _
            (_root_.Fo.colsK gk'.shape lm (_root_.Fo.rdL Reading.gl gk'.zb1) nu) (fun col hc => by
              rw [hb]
              exact H.bit1 col hc), e1]
          exact k2
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [countK_congr gk'.shape lm _ (Cb.Fo.Pin.pinColK lm nu) (fun col hc => by
              rw [hp]
              exact H.pin col hc)]
          exact k3
        · exact absurd hx (by simp)
      rw [hforms] at hf
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
      have h0 := hz _ (List.mem_map_of_mem hc)
      refine (Sound.value_eq (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW)))
        (G'.worldOf Reading.gl (fun j => nu (.mask j))
        (worldOwn a R.late (St.at1 s (Sound.dataQ own a rdW))).entry) c.form (fun _ _ => rfl)
        fun x hx => ?_).trans h0
      have hinc := hall c.form (by rw [hforms]; exact List.mem_map_of_mem hc)
      have h1 : (c.form.slots.toList.all fun x =>
          K9.slotIn own (K9.mergeOf s) R.late a x.1) = true :=
        (Eq.mp (Bool.and_eq_true _ _) hinc).2
      have h2 := List.all_eq_true.1 h1 x hx
      unfold K9.slotIn at h2
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
      show slotW a.F R.late _ x.1 = _
      rw [hlate, slot_late hLG, hmask a ha x.1 h2.1]
      · rfl
      · rw [← hlate]
        rcases h2.2.2.2 with q | q
        · exact Or.inl q
        · exact Or.inr q.1

/-- **"planes": `planes_arm` the other way.** Here s is the verifier's state in front of the head's
own sub-protocol and t the state behind its acceptance. Conditional on the hypotheses of the
library's `planes_arm` but for the item; on the public test behind; on what the lookup on the calls
left at s (`K3LeftAt`); and on the conclusion of `planes_arm` itself at s. No instance of these
hypotheses is exhibited in this file. -/
theorem planes_arm_back (W : OnBytes.Model.Verify.Public) (l : Nat) (blk : Block S Unit)
    (hb : blockOf W l = some blk) (s t : S) (rs₀ : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below blk).decide s rs₀ gs = .ok t)
    (hOn : K6On W s) (P : K8.ReadsQuiet.PH) (b : Nat) (states : Nat → List (RunOf S))
    (hSt : PlanesStates (readsOf W) P.h.lmbH states b) (Rd : Readers) (St : Sound.Stated)
    (own : List (Nat × Nat)) (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms b "planes" t = k6Silent P states b "planes" t)
    (hin : K9.formsInT Rd own b "planes" t = true) (cells : S → Bound K → NCells)
    (nuL : S → Bound K → _root_.Fo.Pl → K) (a : K9.Part) (ha : segAt? t = some a)
    (hmask : ∀ j, j < a.F.ns → (St.at1 t (Sound.dataQ own a rdW)).mask j =
      nuL t (Sound.dataQ own a rdW) (.mask j))
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 t (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells P.h.lmbH nuL t (Sound.dataQ own a rdW) cU 0 pos)
    (hwide : ∀ e F tr, withTables P t = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, t.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - P.h.lmbH) ≤
        (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
          ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (fs : OnBytes.Model.Forest.Shape) (hsh : ∀ g, s.lookHeard? = some g → g.shape = fs)
    (hok : FoNums.ok fs = true) (first : Nat)
    (Q : Fork → Prop)
    (hL : K3LeftAt (fun s : S => s.fork?) (fun s : S => s.lookHeard?) fs P.h.lmbH first Q s)
    (hw : ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.fork? = some F' →
      s.lookHeard? = some g →
      K3OutPlanes fs P.h.lmbH first (nuL t (Sound.dataQ own a rdW)) Reading.gl g F') :
    Sound.formsTQ Rd St own b "planes" t rdW := by
  obtain ⟨F, F', g, rs, _, hnext, hK, hg, hF'⟩ := hL
  obtain ⟨Fs, Ft, f1, f2, hLt, hWl, hh⟩ := below_ledgers W l blk hb s t rs₀ gs h hOn
  obtain rfl : Fs = F' := Option.some.inj (f1.symm.trans hF')
  obtain rfl := hsh g hg
  have hI := hK.heardIs
  rw [hnext] at hI
  refine forms_of_outPlanes W P P.h.lmbH b states hSt Rd St own t rdW hRd hin
    (nuL t (Sound.dataQ own a rdW)) (fun a' ha' j hj => ?_)
    (host_statedAll W P cells nuL St own t rdW a ha cU hArr hcell hwide hlen) g (hh.trans hg) hok
    Fs first (fun F₁ hF₁ => ?_) rs hI (hw g Fs f1 hg)
  · obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
    exact hmask j hj
  · obtain rfl : Ft = F₁ := Option.some.inj (f2.symm.trans hF₁)
    exact ⟨⟨hLt.next, hLt.ns, hLt.keep⟩, ⟨hWl.2.1, hWl.2.2, hWl.1⟩⟩

/-- **The same with what the lookup left in the form of the table's own public item "left".**
Conditional on the same, with `k3LeftItemAt` at s, and on the place's shape, packing and first slot
being the letters'. No instance of these hypotheses is exhibited in this file. -/
theorem planes_arm_back_item (W : OnBytes.Model.Verify.Public) (l : Nat) (blk : Block S Unit)
    (hb : blockOf W l = some blk) (s t : S) (rs₀ : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below blk).decide s rs₀ gs = .ok t)
    (hOn : K6On W s) (P : K8.ReadsQuiet.PH) (b : Nat) (states : Nat → List (RunOf S))
    (hSt : PlanesStates (readsOf W) P.h.lmbH states b) (Rd : Readers) (St : Sound.Stated)
    (own : List (Nat × Nat)) (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : Rd.forms b "planes" t = k6Silent P states b "planes" t)
    (hin : K9.formsInT Rd own b "planes" t = true) (cells : S → Bound K → NCells)
    (nuL : S → Bound K → _root_.Fo.Pl → K) (a : K9.Part) (ha : segAt? t = some a)
    (hmask : ∀ j, j < a.F.ns → (St.at1 t (Sound.dataQ own a rdW)).mask j =
      nuL t (Sound.dataQ own a rdW) (.mask j))
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 t (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells P.h.lmbH nuL t (Sound.dataQ own a rdW) cU 0 pos)
    (hwide : ∀ e F tr, withTables P t = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, t.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - P.h.lmbH) ≤
        (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
          ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (fs : OnBytes.Model.Forest.Shape) (hsh : ∀ g, s.lookHeard? = some g → g.shape = fs)
    (hok : FoNums.ok fs = true) (first : Nat)
    (hL : k3LeftItemAt W l s)
    (hp : ∀ p, First.Look.placeAt W l false = some p →
      p.shape = some fs ∧ p.lm = P.h.lmbH ∧ p.first = first)
    (hw : ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.fork? = some F' →
      s.lookHeard? = some g →
      K3OutPlanes fs P.h.lmbH first (nuL t (Sound.dataQ own a rdW)) Reading.gl g F') :
    Sound.formsTQ Rd St own b "planes" t rdW := by
  obtain ⟨p, hpl, ⟨h', e', hA⟩, _⟩ := hL
  obtain ⟨p1, p2, p3⟩ := hp p hpl
  have e2 : h' = fs := Option.some.inj (e'.symm.trans p1)
  rw [e2, p2, p3] at hA
  exact planes_arm_back W l blk hb s t rs₀ gs h hOn P b states hSt Rd St own rdW hRd hin cells nuL
    a ha hmask cU hArr hcell hwide hlen fs hsh hok first _ hA hw

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.forms_of_outPlanes
#print axioms ProofFile.Honest.K3.Law.Total.planes_arm_back
#print axioms ProofFile.Honest.K3.Law.Total.planes_arm_back_item
