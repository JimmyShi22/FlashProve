-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/BigAt.lean: what the makers of the key file's and the proof file's protocol take
(`FilesParameters`, OnBytes/Flat/FilesAt.lean), AT THE PLAN'S OWN VALUES: the two files' chains and the depth of
a batch's tree are those that the program plans from three public files.

The entry file's chain hangs on the first lines of the parameter file alone, so it has typed values.
The key file's and the proof file's chains hang on all three public files: the verifier's own plans
make the links' oracle messages, the layout and the sub-proofs' rounds of the scale file and the
layout file. So here no value is written out. The values are what the program's own planner
(`Model.Verify.planned`) answers at the public files Z.

Main definitions.
 `planOf Z`       the planner's answer at Z's three files.
 `AtPlan Z G`     G's chains of the key file and of the proof file, and its depth of a batch's tree,
                  are those of the planner's yes at Z. A predicate: where the planner refuses Z it
                  holds of no G, and no made-up value stands in a term.
 `bigAt p …`      the value of `FilesParameters` with these three fields from a planner's answer p; the other
                  four fields are arguments.
Main theorems.
 `atPlan_bigAt`   `AtPlan Z (bigAt p …)` where the planner's answer at Z is p.
 `atPlan_unique`  two values that are at the plan of one Z agree in the three fields.
 `atPlan_port`    **the tie to the program.** At a yes of the program (`PortYesAt`,
                  OnBytes/K/Top.lean) on files whose three public files are Z's: if G is at the
                  plan of Z, then the program's own check of the key file is `Key.check G.k` and
                  said yes with the first table, and its check of the proof file ran at `G.c`, on
                  the links' block at `G.c.first`, and accepted; the links as built, the public
                  values and the layout in that block are those of the planner's answer at Z.
 `atPlan_served`  a served statement (`servedAt Z x`, OnBytes/K/Served.lean) has Z's three files,
                  and the planner says yes at Z: so some G is at the plan of Z.

Not claimed here: soundness or hiding. What the numbers are: no theorem here says what the depth is
at a given parameter file. Anything on the other four fields of `FilesParameters`
(the block of a proof's first chain, the two sample values, what of an instance comes early). For
proofs only; no program imports this file.

-/
import OnBytes.Flat.FilesAt
import OnBytes.K.Top
import OnBytes.K.Served

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.K (PortYesAt UserStm servedAt)

/-- The planner's answer at three public files. -/
def planOf (Z : OnBytes.K.Pub) : Except String Model.Verify.Planned :=
  Model.Verify.planned Z.pol Z.KL (some Z.lay)

/-- **G is at the plan of Z.** -/
def AtPlan {X R : Type} (Z : OnBytes.K.Pub) (G : FilesParameters X R) : Prop :=
  ∃ p, planOf Z = .ok p ∧ G.k = p.chains.key ∧ G.c = p.chains.proof ∧
    G.depthReq = p.chains.proof.first.binding.logLeaves

/-- The value with the three fields from a planner's answer. -/
def bigAt {X R : Type} (p : Model.Verify.Planned) (block : X → Blk Proof.FirstEnd) (rec₀ : R)
    (z₀ : X × R) (early : X → X) : FilesParameters X R where
  k := p.chains.key
  c := p.chains.proof
  block := block
  rec₀ := rec₀
  z₀ := z₀
  depthReq := p.chains.proof.first.binding.logLeaves
  early := early

/-- It is at the plan. -/
theorem atPlan_bigAt {X R : Type} {Z : OnBytes.K.Pub} {p : Model.Verify.Planned}
    (h : planOf Z = .ok p) (block : X → Blk Proof.FirstEnd) (rec₀ : R) (z₀ : X × R)
    (early : X → X) : AtPlan Z (bigAt p block rec₀ z₀ early) :=
  ⟨p, h, rfl, rfl, rfl⟩

/-- Two values at the plan of one Z agree in the three fields. -/
theorem atPlan_unique {X R X' R' : Type} {Z : OnBytes.K.Pub} {G : FilesParameters X R} {G' : FilesParameters X' R'}
    (h : AtPlan Z G) (h' : AtPlan Z G') :
    G.k = G'.k ∧ G.c = G'.c ∧ G.depthReq = G'.depthReq := by
  obtain ⟨p, hp, a, b, c⟩ := h
  obtain ⟨p', hp', a', b', c'⟩ := h'
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  exact ⟨a.trans a'.symm, b.trans b'.symm, c.trans c'.symm⟩

/-- **The tie to the program**: at a yes of the program on files with Z's three public files, the
program's checks of the key file and of the proof file ran at G's chains, and all else that the
check of the proof file was handed is made of the planner's answer p at Z and of the request. -/
theorem atPlan_port {X R : Type} {Z : OnBytes.K.Pub} {G : FilesParameters X R} (hG : AtPlan Z G)
    {F : OnBytes.K.Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further)
    (hp : F.pol = Z.pol) (hy : F.lay = Z.lay) (hk : F.KL = Z.KL) :
    ∃ p, planOf Z = .ok p ∧ Key.check G.k F.key = .ok table ∧
      ∃ so cov item links,
        Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
          .ok so ∧
        Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
        Proof.requestItem F.pol F.KL F.request = some item ∧
        Model.Verify.linksOf p.X cov = .ok links ∧
        Proof.check G.c further F.entry item F.request (Model.ofNat so.y)
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links) G.c.first
            p.X.layers.wsLay) F.proof = .accepted := by
  obtain ⟨p, hpl, a, b, -⟩ := hG
  obtain ⟨-, p', C, -, -, -, -, -, -, -, -, -, -, hp', -, -, hkey, -,
    ⟨so, cov, item, links, h1, h2, h3, h4, h5⟩, -, -, -, -, ⟨hX, hB⟩, -⟩ := h
  have hpl' := hpl
  unfold planOf at hpl'
  rw [← hp, ← hy, ← hk] at hpl'
  obtain rfl : p = p' := Except.ok.inj (hpl'.symm.trans hp')
  rw [hX] at h1 h2 h4 h5
  rw [hB] at h5
  rw [a, b]
  exact ⟨p, hpl, hkey, so, cov, item, links, h1, h2, h3, h4, h5⟩

/-- A served statement has Z's three public files, and the planner says yes at Z. -/
theorem atPlan_served {Z : OnBytes.K.Pub} {x : UserStm} (h : servedAt Z x = true) :
    (x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL) ∧ ∃ p, planOf Z = .ok p := by
  unfold servedAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, -⟩, hm⟩ := h
  refine ⟨⟨e1, e2, e3⟩, ?_⟩
  unfold planOf
  rw [← e1, ← e2, ← e3]
  cases hq : Model.Verify.planned x.pol x.KL (some x.lay) with
  | ok p => exact ⟨p, rfl⟩
  | error e =>
    rw [hq] at hm
    split at hm <;> simp_all

end OnBytes.Flat

#print axioms OnBytes.Flat.atPlan_unique
#print axioms OnBytes.Flat.atPlan_port
#print axioms OnBytes.Flat.atPlan_served
