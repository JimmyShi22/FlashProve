-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefFactG.lean: from the wide fact on fresh masks to the fact that a masked block
needs, for blocks whose reading is any function of entries: virtual names allowed. (not all
hypotheses are named here: see `Spec.segWide_readG`)

Definitions, three statements and their proofs. A rule of the framework only; nothing of a text is
rendered here.
A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of
type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. "Fresh" is
`Chain.FreshGiven`, defined there too.
The wide fact is `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean).
A masked block: `GoodM`, `MaskData` (Ior/Masked.lean); the fact that it needs: `MaskData.fact`
(Cb/Req1/LdSegFresh.lean); the wide reading: `Sig.wide` (Cb/Req1/LdSegCarry.lean).

Why: Cb/Req1/LdSegRefFact.lean (`segWide_read`) asks that the names J of a block's reading hold all
entries of the messages, and that what stands at other names does not depend on the messages. The
blocks at the front of a segment read the messages through a free map (a name may be virtual: a key
computed off a packed cell). The rule in that generality:
  what is read of a witness: kc w j = rdJ (messages, further witness) j if RdJ j, and 0 otherwise
  the own masks stand at entries at' i of the messages, and are read as they are at the names plJ i
    (different names): rdJ (m, wp) (plJ i) = entry at' i of m
  at every other name that the block reads, rdJ (m, wp) j is the same for messages that agree on
    the entries of the wide reading that are not own: any function of these and of the further
    witness
  own masks: put M k = k overwritten at the names plJ i by ve M i (`Function.extend`)

Main names (Mk is finite and not empty in the statements):
  `Spec.segWide_readG`: for this shape, after any chain: if the wide fact is fresh, with every
    at' i own and in the wide reading, val M (at' i) = ve M i, every plJ i read by the block: then
    the block's fact is fresh. (That no other entry is own is not asked: further own entries are
    simply not seen by the block.)
  The same, with the parameters bundled, for whoever puts blocks and facts together:
  `LdReadG a Mk J`: the data of such a reading: Ix, plJ, at', ve, RdJ, rdJ.
  `G.Fits kc' put'`: the block's side: the names plJ i are different and read; at them the entries
    at' i are read as they are; kc' is rdJ cut to RdJ; put' overwrites at plJ.
  `G.Under Rd own val`: the wide reading's side: at other names that the block reads, rdJ is a
    function of the entries in Rd that are not own and of the further witness; every at' i is own
    and in Rd; val M (at' i) = ve M i.
  `a.Narrows X`: a set X of facts is closed under the rule: with the wide fact it holds the block's
    fact.
  `Spec.segWide_narrows`: the facts that are fresh after a chain are such a set.
  `Spec.readG_quiet`: under `G.Fits kc' put'`: overwriting the block's masks changes no entry that
    another reading (msg, Rd') shows, if that reading is a function of what the block reads at
    names that are no own places ("nested readings": the later block's reading shows all that the
    earlier one reads, and the earlier one reads none of its masks).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

/-- States, under the hypotheses below: the wide fact gives the fact of a block whose reading is any
function of entries. -/
def Spec.segWide_readG : Prop :=
  ∀ (E Kc : Type) [Field E] (A : Joint Kc) (a : LdStage E Kc) (c : Chain Kc A a.J)
      (base : MaskFact A.W → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) (J Ix : Type) (plJ : Ix → J)
      (at' : Ix → a.S.Ent) (ve : Mk → Ix → E) (RdJ : J → Prop) (rdJ : a.S.Msg × a.Wp → J → E)
      (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E),
    Function.Injective plJ → (∀ m wp i, rdJ (m, wp) (plJ i) = a.S.ents m (at' i)) →
    (∀ m m' wp j, RdJ j → (∀ i, plJ i ≠ j) →
      (∀ n : a.S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2) → rdJ (m', wp) j = rdJ (m, wp) j) →
    (∀ w j, RdJ j → kc' w j = rdJ (a.S.msgs w.1, w.2) j) → (∀ w j, ¬ RdJ j → kc' w j = 0) →
    (∀ M k, put' M k = Function.extend plJ (ve M) k) → (∀ i, own (at' i)) → (∀ i, Rd (at' i)) →
    (∀ M i, val M (at' i) = ve M i) → (∀ i, RdJ (plJ i)) →
    c.FreshGiven base (a.wideFact Rd Rr own Mk val) → c.FreshGiven base ⟨J → E, kc', Mk, put'⟩

open Classical in
theorem segWide_readG : Spec.segWide_readG := by
  intro E Kc _ A a c base Rd Rr own Mk _ _ val J Ix plJ at' ve RdJ rdJ kc' put' hinj hp1 hp2 hk1 hk0
    hput hown hRd hval hpl h
  let g : (a.wideFact Rd Rr own Mk val).Kc → J → E := fun k j =>
    if RdJ j then rdJ (k.1, k.2.2) j else 0
  have hc := freshGiven_conseq Kc A a.J c base (a.wideFact Rd Rr own Mk val) (J → E) g put' ?_ h
  · have ek : (fun w => g ((a.wideFact Rd Rr own Mk val).kc w)) = kc' := by
      funext w j
      show (if RdJ j then rdJ (a.S.cut Rd (a.S.msgs w.1), w.2) j else 0) = kc' w j
      by_cases hj : RdJ j
      · rw [if_pos hj, hk1 w j hj]
        by_cases hi : ∃ i, plJ i = j
        · obtain ⟨i, rfl⟩ := hi
          rw [hp1, hp1]
          show (if Rd ⟨(at' i).1, (at' i).2⟩ then a.S.msgs w.1 (at' i).1 (at' i).2 else 0) = _
          rw [if_pos (hRd i)]
          rfl
        · refine hp2 _ _ _ j hj (fun i e => hi ⟨i, e⟩) fun n hn _ => ?_
          show (if Rd ⟨n.1, n.2⟩ then a.S.msgs w.1 n.1 n.2 else 0) = _
          rw [if_pos hn]
      · rw [if_neg hj, hk0 w j hj]
    rw [ek] at hc
    exact hc
  · intro M k
    funext j
    rw [hput]
    show (if RdJ j then rdJ (a.S.ow own (val M) k.1, k.2.2) j else 0) = _
    by_cases hi : ∃ i, plJ i = j
    · obtain ⟨i, rfl⟩ := hi
      rw [hinj.extend_apply (ve M) (g k) i, if_pos (hpl i), hp1]
      show (if own ⟨(at' i).1, (at' i).2⟩ then val M ⟨(at' i).1, (at' i).2⟩
          else k.1 (at' i).1 (at' i).2) = _
      rw [if_pos (hown i)]
      exact hval M i
    · rw [Function.extend_apply' _ _ _ hi]
      show _ = if RdJ j then rdJ (k.1, k.2.2) j else 0
      by_cases hj : RdJ j
      · rw [if_pos hj, if_pos hj]
        refine hp2 _ _ _ j hj (fun i e => hi ⟨i, e⟩) fun n _ hn => ?_
        show (if own ⟨n.1, n.2⟩ then val M ⟨n.1, n.2⟩ else k.1 n.1 n.2) = _
        rw [if_neg hn]
      · rw [if_neg hj, if_neg hj]

/-- The data of a reading that is any function of entries. -/
structure LdReadG {E Kc : Type} [Field E] (a : LdStage E Kc) (Mk J : Type) : Type 1 where
  Ix  : Type
  plJ : Ix → J
  at' : Ix → a.S.Ent
  ve  : Mk → Ix → E
  RdJ : J → Prop
  rdJ : a.S.Msg × a.Wp → J → E

namespace LdReadG
variable {E Kc : Type} [Field E] {a : LdStage E Kc} {Mk J : Type} (G : LdReadG a Mk J)

/-- The block's side. -/
structure Fits (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E) : Prop where
  inj : Function.Injective G.plJ
  p1  : ∀ m wp i, G.rdJ (m, wp) (G.plJ i) = a.S.ents m (G.at' i)
  k1  : ∀ w j, G.RdJ j → kc' w j = G.rdJ (a.S.msgs w.1, w.2) j
  k0  : ∀ w j, ¬ G.RdJ j → kc' w j = 0
  put : ∀ M k, put' M k = Function.extend G.plJ (G.ve M) k
  rdP : ∀ i, G.RdJ (G.plJ i)

/-- The wide reading's side. -/
structure Under (Rd own : a.S.Ent → Prop) (val : Mk → a.S.Ent → E) : Prop where
  p2  : ∀ m m' wp j, G.RdJ j → (∀ i, G.plJ i ≠ j) →
    (∀ n : a.S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2) → G.rdJ (m', wp) j = G.rdJ (m, wp) j
  own : ∀ i, own (G.at' i)
  rd  : ∀ i, Rd (G.at' i)
  val : ∀ M i, val M (G.at' i) = G.ve M i

end LdReadG

/-- A set of facts that is closed under the rule. -/
def LdStage.Narrows {E Kc : Type} [Field E] (a : LdStage E Kc) (X : MaskFact a.J.W → Prop) : Prop :=
  ∀ (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → a.S.Ent → E) (J : Type) (G : LdReadG a Mk J)
      (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E),
    G.Fits kc' put' → G.Under Rd own val →
    X (a.wideFact Rd Rr own Mk val) → X ⟨J → E, kc', Mk, put'⟩

namespace Spec

def segWide_narrows : Prop :=
  ∀ (E Kc : Type) [Field E] (A : Joint Kc) (a : LdStage E Kc)
      (c : Chain Kc A a.J) (base : MaskFact A.W → Prop),
    a.Narrows (c.FreshGiven base)

/-- States, under the hypotheses below: nested readings give "quiet" (`ldQuiet`,
Cb/Req1/LdSegFrontTabZk.lean). -/
def readG_quiet : Prop :=
  ∀ (E Kc : Type) [Field E] (a : LdStage E Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (J : Type)
      (G : LdReadG a Mk J) (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E) (J' : Type)
      (msg : a.S.Msg → J' → E) (Rd' : J' → Prop),
    G.Fits kc' put' →
    (∀ m m' wp wp', (∀ j, G.RdJ j → (∀ i, G.plJ i ≠ j) → G.rdJ (m', wp') j = G.rdJ (m, wp) j) →
      ∀ y, Rd' y → msg m' y = msg m y) →
    ∀ (w w' : a.J.W) (M : Mk),
      kc' w' = put' M (kc' w) → ∀ y, Rd' y → msg (a.S.msgs w'.1) y = msg (a.S.msgs w.1) y

end Spec

theorem segWide_narrows :
    Spec.segWide_narrows := fun E Kc _ A a c base Rd Rr own Mk _ _ val J G kc' put' hF hU h =>
  segWide_readG E Kc A a c base Rd Rr own Mk val J G.Ix G.plJ G.at' G.ve G.RdJ G.rdJ kc' put' hF.inj
    hF.p1 hU.p2 hF.k1 hF.k0 hF.put hU.own hU.rd hU.val hF.rdP h

theorem readG_quiet : Spec.readG_quiet := by
  intro E Kc _ a Mk _ _ J G kc' put' J' msg Rd' hF hN w w' M hw y hy
  refine hN _ _ w.2 w'.2 (fun j hj hi => ?_) y hy
  have e := congrFun hw j
  rw [hF.put, Function.extend_apply' _ _ _ (fun ⟨i, hi'⟩ => hi i hi'),
    hF.k1 w' j hj, hF.k1 w j hj] at e
  exact e

end Cb
