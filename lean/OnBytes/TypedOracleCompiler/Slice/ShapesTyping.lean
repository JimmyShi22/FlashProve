-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean: a file's checker by the way "type, then run": its clause `fit`,
once for all.

`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) asks of a file's part the clause `fit`: the
compiled verifier accepts what the checker returns, under the family read out of the oracle through
the part's implementation. A checker can be filled in two ways. It can be a second text of the
program's check on bytes: then `fit` is a theorem on that text, for every oracle and all tables. Or
it can TYPE the file (asking the oracle where the typed string holds values of the hash) and then
RUN the part's typed verifier over the one oracle through the implementation, and return the
typing's value where that run says yes. This file is about the second way: there `fit` holds by
construction, but for one thing: the checker runs under the oracle with the public tables put over
it, and `fit` speaks of the family read out of the oracle beneath.

Main definitions: `chkT`, `withTyping`, `FileSpec.ofTyping`.
Main theorems.
 `det_overOne` an algorithm without coins, run over the one oracle through an implementation, has
     the value that it has under the family read out of the oracle.
 `readBlocks_over` that family does not see a table at a typed query none of whose strings is in the
     table's set.
 `chkT_det`, `chkT_noCoin`, `chkT_queries`.
 `chkT_fit`, `FileSpec.ofTyping_fit` `fit`, from `clean` (no typed query of the verifier's run has a
     public string) and `okT` (what the typing returns is `ok`). No condition on clashes.

The price: the checker's count of strings takes in the verifier's typed queries, B strings each, B a
bound on the blocks of an answer; it stands in the part's bound.

What is not claimed. No typing is given. `clean` is a hypothesis: it is owed by whoever gives the
implementation. That the program's yes makes the typing succeed and the typed verifier accept is no
matter of this file: it is owed at the format's own hash alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Shapes
import OnBytes.Slice.DetLog
import Rom.NoCoinExits

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob MeasureTheory
open scoped ENNReal

/-- An algorithm without coins, run over the one oracle through an implementation, has under g the
value that it has under the family read out of g. -/
theorem det_overOne {S : OSpec} {lam : ℕ} {α : Type} (m : OracleCoding S lam) (g : Fam (rom lam))
    (c : OComp S α) (hc : c.NoCoin) : (c.overOne m).det g = c.det (readBlocks m g) := by
  have h := runEager_overOne m g c
  rw [(noCoin_overOne m c hc).runEager g, hc.runEager (readBlocks m g)] at h
  have h1 : (c.overOne m).det g ∈ (PMF.pure (c.det (readBlocks m g))).support :=
    h ▸ (PMF.mem_support_pure_iff _ _).2 rfl
  exact (PMF.mem_support_pure_iff _ _).1 h1

/-- The family read out of an oracle with a table put over it is, at a typed query none of whose
strings lies in the table's set, the family read out of the oracle. -/
theorem readBlocks_over {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (P : Finset (List Bool))
    (T : List Bool → Dig lam) (g : Fam (rom lam)) (o : S.ι) (q : S.Dom o)
    (h : ∀ j, m.code o q j ∉ P) : readBlocks m (over P T g) o q = readBlocks m g o q := by
  unfold readBlocks
  congr 1
  funext j
  rw [over_not_mem _ _ (h j)]

namespace Shapes

/-- The checker of the way "type, then run": the typing, which may ask the oracle; then the
part's typed verifier on what the typing returns, run over the one oracle through the part's
implementation; the typing's value where that run says yes. -/
def chkT (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (x : Files) : OComp (rom 256) (Option p.Out) :=
  (typ x).bind fun
    | none => OComp.pure none
    | some o => ((p.J.run o).overOne p.m).bind fun b => OComp.pure (if b then some o else none)

/-- Its value: the typing's, where the typed verifier accepts under the family read out of the
oracle. -/
theorem chkT_det (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (x : Files) (g : Fam (rom 256)) (o : p.Out)
    (h : (chkT p typ x).det g = some o) :
    (typ x).det g = some o ∧ (p.J.run o).det (readBlocks p.m g) = true := by
  unfold chkT at h
  rw [OComp.det_bind] at h
  rcases ht : (typ x).det g with _ | o'
  · rw [ht] at h
    cases h
  · rw [ht] at h
    have h' : (((p.J.run o').overOne p.m).bind fun b =>
        OComp.pure (if b then some o' else none)).det g = some o := h
    rw [OComp.det_bind, det_overOne p.m g _
      (noCoin_of_detBound _ _ (p.J.bound o'))] at h'
    have h'' : (if (p.J.run o').det (readBlocks p.m g) then some o' else none) = some o := h'
    by_cases hb : (p.J.run o').det (readBlocks p.m g) = true
    · rw [if_pos hb] at h''
      cases h''
      exact ⟨rfl, hb⟩
    · rw [if_neg hb] at h''
      cases h''

/-- A part with that checker. tT bounds the typing's strings, B the blocks of an answer: the
count of the checker's strings takes in the verifier's typed queries, B strings each. -/
def withTyping (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (tT B : ℕ) :
    TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX :=
  { p with chk := chkT p typ, tR := tT + (p.J.tV * B + 0) }

/-- It tosses no coin, if the typing tosses none. -/
theorem chkT_noCoin (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (hn : ∀ x, (typ x).NoCoin) (x : Files) :
    (chkT p typ x).NoCoin :=
  OComp.NoCoin.bind (hn x) fun a => by
    cases a with
    | none => exact trivial
    | some o =>
      exact OComp.NoCoin.bind (noCoin_overOne p.m _ (noCoin_of_detBound _ _ (p.J.bound o)))
        fun _ => trivial

/-- It asks at most tT + tV * B strings. -/
theorem chkT_queries (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (tT B : ℕ)
    (hq : ∀ x, (typ x).QueryBound tT) (hB : ∀ o, p.m.blocks o ≤ B) (x : Files) :
    (chkT p typ x).QueryBound (tT + (p.J.tV * B + 0)) :=
  OComp.QueryBound.bind (hq x) fun a => by
    cases a with
    | none =>
      show (OComp.pure none : OComp (rom 256) (Option p.Out)).QueryBound _
      exact trivial
    | some o =>
      exact OComp.QueryBound.bind
        (queryBound_overOne p.m hB _ _ (p.J.bound o).queryBound) fun _ => trivial

/-- FIT, ONCE FOR ALL, for the way "type, then run". Asked: `clean`: no typed query of the
verifier's run has a string in the public set; `okT`: what the typing returns is `ok`. No condition
on clashes. -/
theorem chkT_fit (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (P : Finset (List Bool)) (T : Tab)
    (clean : ∀ (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 p.W.K p.L)) (o : p.Out),
      ∀ e ∈ ((p.J.run o).withTrace.det F).2, ∀ j, p.m.code e.1 e.2.1 j ∉ P)
    (okT : ∀ (g : Fam (rom 256)) (x : Files) (o : p.Out), (typ x).det g = some o → p.J.ok o)
    (g : Fam (rom 256)) (x : Files) (o : p.Out) (h : (chkT p typ x).det (over P T g) = some o) :
    (p.J.run o).det (readBlocks p.m g) = true ∧ p.J.ok o := by
  obtain ⟨ht, hr⟩ := chkT_det p typ x _ o h
  refine ⟨?_, okT _ x o ht⟩
  rw [← hr]
  exact det_eq_of_agree (readBlocks p.m (over P T g)) (readBlocks p.m g) (p.J.run o)
    (fun o' q => ∀ j, p.m.code o' q j ∉ P) (clean _ o)
    fun o' q hq => (readBlocks_over p.m P T g o' q hq).symm

/-- `clean` IN TWO HALVES, each with one owner: the verifier's run never asks the oracle sp
(said once, of the verifier); every public string is, under the implementation, a point of sp (said
of each implementation). -/
theorem clean_of_noOther (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX) (P : Finset (List Bool))
    (sp : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 p.W.K p.L).ι)
    (hrun : ∀ (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 p.W.K p.L)) (o : p.Out),
      ∀ e ∈ ((p.J.run o).withTrace.det F).2, e.1 ≠ sp)
    (hS : ∀ s ∈ P, (p.m.inv s).1 = sp)
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 p.W.K p.L)) (o : p.Out) :
    ∀ e ∈ ((p.J.run o).withTrace.det F).2, ∀ j, p.m.code e.1 e.2.1 j ∉ P := by
  intro e he j hm
  have h1 := hS _ hm
  rw [p.m.inv_code ⟨e.1, e.2.1, j⟩] at h1
  exact hrun F o e he h1

/-- A file's part by the way "type, then run", at all tables: `base` gives interface, wiring,
judge, error, implementation, roots and symbols (its own checker and count are not read); `typ` is
the typing. -/
def FileSpec.ofTyping (base : Tab → Tab → TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option (base T₀ T₁).Out))
    (pre : ∀ T₀ T₁, (o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).ι) →
      (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (base T₀ T₁).W.K (base T₀ T₁).L).Dom o →
      TypedOracleCompiler.Compile.Batch.TypedOracleComputation 256 (base T₀ T₁).W.K (base T₀ T₁).L Unit)
    (n tT B : ℕ) : FileSpec where
  part := fun T₀ T₁ => withTyping (base T₀ T₁) (typ T₀ T₁) tT B
  pre := pre
  n := n

/-- Its clause `fit`, in the form in which `FileSpec.Delivers` asks it. Asked: at all tables no
typed query of the verifier's run has a public string; what the typing returns is `ok`. -/
theorem FileSpec.ofTyping_fit (base : Tab → Tab → TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option (base T₀ T₁).Out))
    (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (clean : ∀ T₀ T₁ (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (base T₀ T₁).W.K
        (base T₀ T₁).L)) (o : (base T₀ T₁).Out),
      ∀ e ∈ (((base T₀ T₁).J.run o).withTrace.det F).2,
        ∀ j, (base T₀ T₁).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀)
    (okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : (base T₀ T₁).Out),
      (typ T₀ T₁ x).det g = some o → (base T₀ T₁).J.ok o)
    (T₀ T₁ : Tab) (g : Fam (rom 256)) (x : Files) (o : (base T₀ T₁).Out)
    (h : (chkT (base T₀ T₁) (typ T₀ T₁) x).det (over (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) g) = some o) :
    ((base T₀ T₁).J.run o).det (readBlocks (base T₀ T₁).m g) = true ∧ (base T₀ T₁).J.ok o :=
  chkT_fit (base T₀ T₁) (typ T₀ T₁) _ _ (clean T₀ T₁) (okT T₀ T₁) g x o h

end Shapes

end OnBytes.Slice
