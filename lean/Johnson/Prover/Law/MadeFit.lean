-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/MadeFit.lean: THREE PUBLIC FACTS ON THE DATA OF A WHOLE FILE THAT HAVE PASSED THE
MAKERS' TESTS, and what the first gives at the file's wire record: at most two trees a round; as
many items "root" as trees; no tree deeper than 63. So FewJ and Few0
(OnBytes/TypedOracleCompiler/Joined/K/RunSome.lean), two premises of (T1) yes_of_prove (OnBytes/Prover/Main.lean),
hold at wqWhole (OnBytes/Maker/Wire.lean).

Why. OnBytes/Maker/FitsFew.lean has the wire's half chain by chain, and says in its limits: "That
any data's rounds send at most maxRt trees is not shown". A description's data are made behind the
test okAt (FileDescription.data, Johnson/Desc/BlockSlot.lean), which holds Three.Whole.fits at 2.

Main names.
  MadeFit   the three facts, as one record.
  roots_of   by construction: WholeD.of lays as many trees as the message has items "root", in all
    three chains. (of_trees_roots, Johnson/Top/H/LookNoTree.lean [not in this library], has the first chain; that file is
    NOT imported: nineteen files outside the soundness theorem's imports lie beneath it; the step is
    made of two general lemmas of OnBytes/Flat/WholeEntries.lean instead.)
  madeFit_of_ok, madeFit_empty, madeFit_of_data, MadeFit.at   where the tests have said yes; at
    three empty lists; at a description's data; at another depth of the stored table.
  fewJ_app, few0_app, fewJ_wiresSh, few0_wiresLo   the pieces that OnBytes/Maker/FitsFew.lean lacks.
  fewJ_wqWhole, few0_wqWhole   THE TWO PREMISES at the whole file's wire record.

It adds no strength. Calls: okAt_parts, WholeD.depthFit_iff (OnBytes/Maker/Files.lean); fits_trees,
all_of_map, wholeEntries_zipWith_left (OnBytes/Flat/WholeEntries.lean); data_ok
(Johnson/Desc/BlockSlotProofs.lean); fewJ_wiresLo, few0_wiresSh (OnBytes/Maker/FitsFew.lean).

Limits. Nothing on the numbers of rounds or of items, on the binding tree or on a salt's length. The
copy's file is not spoken of. That a description's data are such data at given public files: another
file.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.WholeEntries
import Johnson.Desc.BlockSlotProofs
import OnBytes.Maker.FitsFew
import OnBytes.Maker.Files
import Johnson.EntryRec.OkcFiles

set_option autoImplicit false

namespace OnBytes.Prover
open OnBytes.Params (Rounds)
open OnBytes.Three OnBytes.Maker OnBytes.Flat
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The three facts. -/
structure MadeFit (D : WholeD) : Prop where
  few : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.trees.length ≤ 2
  roots : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.items.countP (· == .root) = d.trees.length
  depths : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ t ∈ d.trees, t.a < 64

/-- **By construction: as many trees as items "root", in all three chains.** -/
theorem roots_of (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₁ ++ ((WholeD.of a (Whole.of R₁ R₂ R₃)).ds₂ ++
      (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₃), d.items.countP (· == .root) = d.trees.length := by
  have key : ∀ (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
      (R : Rounds), ∀ d ∈ rdsFromL all t₁ t₂ here base first R,
        d.items.countP (· == .root) = d.trees.length :=
    fun all t₁ t₂ here base first R =>
      all_of_map (fun d : RDL => (d.items.countP (· == Fmt.Item.root), d.trees.length))
        (fun r : Fmt.Round × List Fmt.Stored =>
          (r.1.items.countP (· == Fmt.Item.root), r.1.items.countP (· == Fmt.Item.root)))
        (fun p => p.1 = p.2)
        (wholeEntries_zipWith_left (rdOf all t₁ t₂ here base first) _ _
          (fun _ _ => by simp [rdOf]) R _ (OnBytes.Flat.sentBefore_length R))
        fun _ _ => rfl
  intro d hd
  rcases List.mem_append.1 hd with h1 | h23
  · have h1' : d ∈ ((Whole.of R₁ R₂ R₃).ds₁.dropLast).map rdtOf := h1
    obtain ⟨d0, h0, rfl⟩ := List.mem_map.1 h1'
    exact key _ _ _ _ _ _ R₁ d0 ((List.dropLast_sublist _).subset h0)
  · rcases List.mem_append.1 h23 with h2 | h3
    · have h2' : d ∈ ((Whole.of R₁ R₂ R₃).ds₂).map rdtOf := h2
      obtain ⟨d0, h0, rfl⟩ := List.mem_map.1 h2'
      exact key _ _ _ _ _ _ R₂ d0 h0
    · have h3' : d ∈ ((Whole.of R₁ R₂ R₃).ds₃).map rdtOf := h3
      obtain ⟨d0, h0, rfl⟩ := List.mem_map.1 h3'
      exact key _ _ _ _ _ _ R₃ d0 h0

/-- Where the makers' tests have said yes. -/
theorem madeFit_of_ok {a : ℕ} {R : Rounds × Rounds × Rounds} (h : okAt a (some R) = true) :
    MadeFit (WholeD.of a (wholeAt (some R))) where
  few := fits_trees a R.1 R.2.1 R.2.2 (okAt_parts h).fits
  roots := roots_of a R.1 R.2.1 R.2.2
  depths := fun d hd t ht =>
    Nat.lt_succ_of_le ((WholeD.depthFit_iff _).1 (okAt_parts h).depth d hd t ht)

/-- At three empty lists. -/
theorem madeFit_empty (a : ℕ) : MadeFit (WholeD.of a (Whole.of [] [] [])) where
  few := fun _ hd => by cases hd
  roots := fun _ hd => by cases hd
  depths := fun _ hd => by cases hd

/-- **At a description's data.** -/
theorem madeFit_of_data {Xi : Type} {F : VerifiableInference.Desc.FileDescription Xi} {file : String}
    {D : WholeD} (h : F.data file = .ok D) : MadeFit D := by
  obtain ⟨R, -, hk, rfl⟩ := VerifiableInference.Desc.data_ok h
  exact madeFit_of_ok hk

/-- At another depth of the stored table: the lists are the same. -/
theorem MadeFit.at {D : WholeD} (h : MadeFit D) (a : ℕ) : MadeFit (D.at a) :=
  ⟨h.few, h.roots, h.depths⟩

/-! ## At the wire record -/

section
variable {lam K : ℕ}

theorem fewJ_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, FewJ s A W → FewJ u B V →
      FewJ (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, fewJ_app hW.2 hV⟩

theorem few0_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, Few0 s A W → Few0 u B V →
      Few0 (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, few0_app hW.2 hV⟩

end

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- A shared written round has no tree of a slot's. -/
theorem fewJ_wiresSh : ∀ ds : List RDT, FewJ _ _ (wiresSh C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨Nat.zero_le _, fewJ_wiresSh ds⟩

/-- A local written round has no shared tree. -/
theorem few0_wiresLo : ∀ ds : List RDT, Few0 _ _ (wiresLo C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨Nat.zero_le _, few0_wiresLo ds⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **FewJ at the wire record of a whole written file.** -/
theorem fewJ_wqWhole (h : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.trees.length ≤ 2) :
    FewJ _ _ (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨Nat.zero_le _,
    fewJ_app (fewJ_wiresLo C K chal D.ds₁ fun d hd => h d (List.mem_append_left _ hd))
      ⟨Nat.zero_le _, fewJ_app (fewJ_wiresSh C K chal D.ds₂)
        ⟨Nat.zero_le _, fewJ_wiresLo C K chal D.ds₃ fun d hd =>
          h d (List.mem_append_right _ (List.mem_append_right _ hd))⟩⟩⟩

/-- **Few0 there.** -/
theorem few0_wqWhole (h : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.trees.length ≤ 2) :
    Few0 _ _ (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨Nat.zero_le _,
    few0_app (few0_wiresLo C K chal D.ds₁)
      ⟨Nat.zero_le _, few0_app (few0_wiresSh C K chal D.ds₂ fun d hd =>
          h d (List.mem_append_right _ (List.mem_append_left _ hd)))
        ⟨Nat.zero_le _, few0_wiresLo C K chal D.ds₃⟩⟩⟩

end

end OnBytes.Prover

#print axioms OnBytes.Prover.roots_of
#print axioms OnBytes.Prover.madeFit_of_ok
#print axioms OnBytes.Prover.madeFit_empty
#print axioms OnBytes.Prover.madeFit_of_data
#print axioms OnBytes.Prover.MadeFit.at
#print axioms OnBytes.Prover.fewJ_wqWhole
#print axioms OnBytes.Prover.few0_wqWhole
