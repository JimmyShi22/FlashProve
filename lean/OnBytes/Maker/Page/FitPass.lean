-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FitPass.lean: the six forms of chain query and the sealing call's query of which
the record `QuietAtQ` (OnBytes/Maker/Page/RowsAtQ.lean) speaks pass the tests of
OnBytes/Maker/Page/FitAt.lean, IF the three silent messages pass the letters' tests: so that record
is met at every pair of conditions that the tests imply.

Definitions that compute, statements and proofs. OnBytes/Maker/Page/FitAt.lean lays a test on typed
chain queries under which a file's calls are one to one. A test that no query of a run passes would
make that law idle. Here: the queries of which `QuietAtQ` speaks pass: at a written round, its own
number, as many roots as it sends trees, its own plain part with a nonce below 2^64; the three first
queries with no roots, at messages that pass the letters' tests; the sealing call's query at the
joining round's part of a slot.

Main names:
  `nRoots l`: the items "root" of a message. `toRoots_some`: a list of that length fits.
  `rootsOK D`: every written round has as many items "root" as it sends trees: a test on the data.
  `fitRow_of`: the test at a written round, from what `partAt` and `rdAt` give.
  `oursEnd_fit`, `oursShE_fit`: along a stretch.
  `slotAt_own`: the sealing call's plain part passes.
  `quietAtQ_fit`: `QuietAtQ`, at every Q and Qg that the tests imply.
  `quietAtQ_part`: at Q := `fitPart` of `fitAt`, Qg := 256 bits, no roots, `slotAt`.
Premises of `quietAtQ_fit`: the read-back undoes the embedding (hrd); the test `rootsOK`; the three
messages pass the letters' tests; salt, request root and the two seals have 256 bits.
No letter stands under "there is".

What is not claimed. That a file's silent messages pass the letters' tests (hF, hJ, h3): for the
front and the joining message at the tests of OnBytes/Maker/Page/FitSilent.lean that asks a law
which ties the outer roots that the verifier lays to the answers that the messages bear. That these
seven forms are all that a typed run asks: where the interface's late names a written round, the
run's query of that round holds an instance, and passes no test here. That the wires' numbers of
trees are those which the forms suppose (none at a silent round; the round's trees at a written
one). That the calls lie in the domain of the format's hash. That the seeds' code is silent at these
queries. That `rootsOK` holds at any data. Nothing on any hash. Nothing on soundness.


-/
import OnBytes.Maker.Page.FitAt
import OnBytes.Maker.Page.RowsAtQ

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open _root_.Run.Twin (allLo allLo_eq)
open _root_.Fmt (Item)
open TypedOracleCompiler.Run.PQ (toRoots)
open OnBytes.K.Arm.FileInj (FitJ fitPart)

/-- The items "root" of a message. -/
def nRoots : List Item → ℕ
  | [] => 0
  | .root :: l => nRoots l + 1
  | _ :: l => nRoots l

/-- A list of as many roots as the message has items "root" fits. -/
theorem toRoots_some : ∀ (l : List Item) (rt : List (Dig 256)), rt.length = nRoots l →
    (toRoots l rt).isSome = true
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | .root :: l, r :: rt, h => by
      show ((toRoots l rt).map fun y => ((r, y) : Dig 256 × RootOf l)).isSome = true
      rw [Option.isSome_map]
      exact toRoots_some l rt (Nat.succ.inj h)
  | .root :: _, [], h => absurd h.symm (Nat.succ_ne_zero _)
  | .f :: l, rt, h => toRoots_some l rt h
  | .word :: l, rt, h => toRoots_some l rt h
  | .e :: l, rt, h => toRoots_some l rt h
  | .answer :: l, rt, h => toRoots_some l rt h

/-- Every written round has as many items "root" as it sends trees. -/
def rootsOK (D : WholeD) : Bool :=
  (D.ds₁ ++ D.ds₂ ++ D.ds₃).all fun d => nRoots d.items == d.trees.length

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- The test at a written round, from what `partAt` and `rdAt` give. -/
theorem fitRow_of {i : ℕ} {rt : List (Dig 256)} {z : PBt L t} {m : List ByteArray → ByteArray}
    {n : ℕ} {d : RDT} (hp : partAt C D tF tJ t3 rd z = .row i m n) (hn : n < 2 ^ 64)
    (hR : rdAt D i = some d) (hl : rt.length = nRoots d.items) :
    fitRow C D tF tJ t3 rd i rt z = true := by
  unfold fitRow
  rw [hp]
  show (decide (i = i) && decide (n < 2 ^ 64) && rootsFit D i rt) = true
  unfold rootsFit
  rw [hR]
  show (decide (i = i) && decide (n < 2 ^ 64) && (toRoots d.items rt).isSome) = true
  rw [toRoots_some _ _ hl, decide_eq_true hn, decide_eq_true rfl]
  rfl

variable (Q : FbIn 256 L t → Prop)

/-- **Along a stretch of local rounds.** -/
theorem oursEnd_fit : ∀ (ds : List RDT) (a : ℕ)
    (e : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs ds)) (allLo (TypedOracleCompiler.Run.PQ.SL C (toRDs ds))) → PBt L t),
    (∀ i ρ rt z, ρ.length = 256 → fitRow C D tF tJ t3 rd i rt z = true →
      Q ⟨i, .f2 none ρ, rt, z⟩) →
    (∀ z, partAt C D tF tJ t3 rd (e z) =
      PartJ.ofSaid a (saidLo C ds (pTo (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds))) z))) →
    (∀ k, k < ds.length → rdAt D (a + 1 + k) = ds[k]?) →
    (∀ d ∈ ds, nRoots d.items = d.trees.length) →
    OursEnd Q C (toRDs ds) e (a + 1)
  | [], _, _, _, _, _, _ => trivial
  | d :: ds, a, e, hQ, hP, hR, hT => by
    refine ⟨fun ρ rt pl h1 h2 h3 => hQ _ ρ rt _ h1
        (fitRow_of C D tF tJ t3 rd (m := (saidOf C d pl).msg) (n := (saidOf C d pl).nonce) (d := d)
          ?_ h3 (hR 0 (Nat.succ_pos _)) (h2.trans (hT d List.mem_cons_self).symm)),
      oursEnd_fit ds (a + 1) (fun z => e (.inr z)) hQ (fun z => ?_) (fun k hk => ?_)
        fun d' hd' => hT d' (List.mem_cons_of_mem _ hd')⟩
    · rw [hP]
      exact congrArg (fun w => PartJ.ofSaid a (saidLo C (d :: ds) w))
        (pTo_inl (RAnn.allLocal (roundT C d).up) (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds)))
          (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs (d :: ds)))) (.inr pl))
    · rw [hP]
      exact (congrArg (fun w => PartJ.ofSaid a (saidLo C (d :: ds) w))
        (pTo_inr (RAnn.allLocal (roundT C d).up) (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs ds)))
          (allLo_eq (TypedOracleCompiler.Run.PQ.SL C (toRDs (d :: ds)))) z)).trans (ofSaid_next a _)
    · have h := hR (k + 1) (Nat.succ_lt_succ hk)
      rw [show a + 1 + (k + 1) = a + 1 + 1 + k by omega] at h
      exact h

/-- **Along a stretch of shared rounds.** -/
theorem oursShE_fit : ∀ (ds : List RDT) (a : ℕ)
    (e : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs ds)) (TypedOracleCompiler.Run.PQ.annShE C (toRDs ds)) → PBt L t),
    (∀ i ρ rt z, ρ.length = 256 → fitRow C D tF tJ t3 rd i rt z = true →
      Q ⟨i, .f5 ρ, rt, z⟩) →
    (∀ z, partAt C D tF tJ t3 rd (e z) =
      PartJ.ofSaid a (saidSh C ds (pTo (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds)) z))) →
    (∀ k, k < ds.length → rdAt D (a + 1 + k) = ds[k]?) →
    (∀ d ∈ ds, nRoots d.items = d.trees.length) →
    OursShE Q C (toRDs ds) e (a + 1)
  | [], _, _, _, _, _, _ => trivial
  | d :: ds, a, e, hQ, hP, hR, hT => by
    refine ⟨fun ρ rt pl h1 h2 h3 => hQ _ ρ rt _ h1
        (fitRow_of C D tF tJ t3 rd (m := (saidOf C d pl).msg) (n := (saidOf C d pl).nonce) (d := d)
          ?_ h3 (hR 0 (Nat.succ_pos _)) (h2.trans (hT d List.mem_cons_self).symm)),
      oursShE_fit ds (a + 1) (fun z => e (.inr z)) hQ (fun z => ?_) (fun k hk => ?_)
        fun d' hd' => hT d' (List.mem_cons_of_mem _ hd')⟩
    · rw [hP]
      exact congrArg (fun w => PartJ.ofSaid a (saidSh C (d :: ds) w))
        (pTo_inl (RAnn.ofShared .sh (roundT C d).up) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds))
          (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs (d :: ds))) (.inl pl))
    · rw [hP]
      exact (congrArg (fun w => PartJ.ofSaid a (saidSh C (d :: ds) w))
        (pTo_inr (RAnn.ofShared .sh (roundT C d).up) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs ds))
          (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs (d :: ds))) z)).trans (ofSaid_next a _)
    · have h := hR (k + 1) (Nat.succ_lt_succ hk)
      rw [show a + 1 + (k + 1) = a + 1 + 1 + k by omega] at h
      exact h

variable (Qg : JoiningRoundQuery 256 L t → Prop)
  (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann → PBt L t)
  (hrd : ∀ w, rd (embP w) = some w)
include hrd

/-- **The sealing call's plain part passes.** -/
theorem slotAt_own (u : Unit) :
    slotAt C D tF tJ t3 rd (e₂ C D tF tJ t3 embP (Sum.inl (Sum.inr u))) = true := by
  show slotAt C D tF tJ t3 rd (embP (in₂ C D tF tJ t3
    (pTo (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
      (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) (Sum.inl (Sum.inr u))))) = true
  unfold slotAt
  rw [hrd]
  exact (congrArg (fun w => isSlot C D tF tJ t3 (in₂ C D tF tJ t3 w))
    (pTo_inl (RAnn.ofShared .sh (plainRound TJ tJ)) (TypedOracleCompiler.Run.PQ.annShE_eq C (toRDs D.ds₂))
      (annL₂ C (plainRS TF tF) (plainRS TJ tJ) (plainRS T3 t3) (RAnn.ofShared .sh _)
        (toRDs D.ds₁) (toRDs D.ds₂) (toRDs D.ds₃)) (Sum.inr u))).trans (isSlot_in C D tF tJ t3)

variable (Sl : SilentJ X TF TJ T3) (fF : List (Dig 256) → Option X → TF → Bool)
  (fJ : List (Dig 256) → TJ → Bool) (f3 : T3 → Bool)

/-- **The file's own queries meet every pair of conditions that the tests imply.** -/
theorem quietAtQ_fit (hT : rootsOK D = true)
    (qLo : ∀ i ρ rt z, ρ.length = 256 → fitRow C D tF tJ t3 rd i rt z = true →
      Q ⟨i, .f2 none ρ, rt, z⟩)
    (qSh : ∀ i ρ rt z, ρ.length = 256 → fitRow C D tF tJ t3 rd i rt z = true →
      Q ⟨i, .f5 ρ, rt, z⟩)
    (q1 : ∀ cms x salt z, frontAt C D tF tJ t3 rd fF cms x z = true → salt.length = 256 →
      Q ⟨0, .f1 cms x salt, [], z⟩)
    (q2 : ∀ cms r z, joinAt C D tF tJ t3 rd fJ cms z = true → r.length = 256 →
      Q ⟨(fillJ C D tF tJ t3 rd Sl).J, .f4 cms r, [], z⟩)
    (q3 : ∀ a c z, seamAt C D tF tJ t3 rd f3 z = true → a.length = 256 → c.length = 256 →
      Q ⟨(fillJ C D tF tJ t3 rd Sl).J3, .f3 a c, [], z⟩)
    (qG : ∀ ρ z, ρ.length = 256 → slotAt C D tF tJ t3 rd z = true →
      Qg ⟨(fillJ C D tF tJ t3 rd Sl).J, ρ, [], z⟩)
    {cms : List (Dig 256)} {x : Option X} {salt rtreq ρ0 c : Bits} {pF : TF} {pJ : TJ} {p3 : T3}
    (hF : fF cms x pF = true) (hs : salt.length = 256) (hJ : fJ cms pJ = true)
    (hr : rtreq.length = 256) (h3 : f3 p3 = true) (ha : ρ0.length = 256) (hc : c.length = 256) :
    QuietAtQ C D tF tJ t3 rd Sl Q Qg embP cms x salt rtreq ρ0 c pF pJ p3 := by
  have hT' : ∀ d ∈ D.ds₁ ++ D.ds₂ ++ D.ds₃, nRoots d.items = d.trees.length := fun d hd =>
    eq_of_beq (List.all_eq_true.1 hT d hd)
  exact
  { one := oursEnd_fit C D tF tJ t3 rd Q D.ds₁ 0 _ qLo (partAt_one C D tF tJ t3 rd embP hrd)
      (fun k hk => rdAt_one D k hk)
      fun d hd => hT' d (List.mem_append_left _ (List.mem_append_left _ hd))
    two := oursShE_fit C D tF tJ t3 rd Q D.ds₂ (D.ds₁.length + 1) _ qSh
      (partAt_two C D tF tJ t3 rd embP hrd) (fun k hk => rdAt_two D k hk)
      fun d hd => hT' d (List.mem_append_left _ (List.mem_append_right _ hd))
    three := oursEnd_fit C D tF tJ t3 rd Q D.ds₃ (D.ds₁.length + D.ds₂.length + 2) _ qLo
      (partAt_three C D tF tJ t3 rd embP hrd) (fun k _ => rdAt_three D k)
      fun d hd => hT' d (List.mem_append_right _ hd)
    first₁ := q1 cms x salt _ (by
      unfold frontAt
      rw [partAt_front C D tF tJ t3 rd embP hrd pF]
      exact hF) hs
    first₂ := q2 cms rtreq _ (by
      unfold joinAt
      rw [partAt_join C D tF tJ t3 rd embP hrd pJ]
      exact hJ) hr
    first₃ := q3 ρ0 c _ (by
      unfold seamAt
      rw [partAt_seam C D tF tJ t3 rd embP hrd p3]
      exact h3) ha hc
    slot := fun ρ hρ => qG ρ _ hρ (slotAt_own C D tF tJ t3 rd embP hrd _) }

/-- **At the tests themselves.** -/
theorem quietAtQ_part (hT : rootsOK D = true) {cms : List (Dig 256)} {x : Option X}
    {salt rtreq ρ0 c : Bits} {pF : TF} {pJ : TJ} {p3 : T3} (hF : fF cms x pF = true)
    (hs : salt.length = 256) (hJ : fJ cms pJ = true) (hr : rtreq.length = 256)
    (h3 : f3 p3 = true) (ha : ρ0.length = 256) (hc : c.length = 256) :
    QuietAtQ C D tF tJ t3 rd Sl
      (fun q => fitPart (fitAt C D tF tJ t3 rd fF fJ f3) q.round q.rt q.plain q.head = true)
      (fun q => q.ρ.length = 256 ∧ q.rt = [] ∧ slotAt C D tF tJ t3 rd q.plain = true) embP cms x
      salt rtreq ρ0 c pF pJ p3 :=
  quietAtQ_fit C D tF tJ t3 rd _ _ embP hrd Sl fF fJ f3 hT
    (fun i ρ rt z h1 h2 => by
      show (ρ.length == 256 && fitRow C D tF tJ t3 rd i rt z) = true
      rw [h2, h1]
      rfl)
    (fun i ρ rt z h1 h2 => by
      show (ρ.length == 256 && fitRow C D tF tJ t3 rd i rt z) = true
      rw [h2, h1]
      rfl)
    (fun cms x salt z h1 h2 => by
      show (([] : List (Dig 256)).isEmpty && frontAt C D tF tJ t3 rd fF cms x z &&
        salt.length == 256) = true
      rw [h1, h2]
      rfl)
    (fun cms r z h1 h2 => by
      show (([] : List (Dig 256)).isEmpty && joinAt C D tF tJ t3 rd fJ cms z &&
        r.length == 256) = true
      rw [h1, h2]
      rfl)
    (fun a c z h1 h2 h3 => by
      show (([] : List (Dig 256)).isEmpty && seamAt C D tF tJ t3 rd f3 z && a.length == 256 &&
        c.length == 256) = true
      rw [h1, h2, h3]
      rfl)
    (fun ρ z h1 h2 => ⟨h1, rfl, h2⟩) hF hs hJ hr h3 ha hc

end

end OnBytes.Maker.Page
