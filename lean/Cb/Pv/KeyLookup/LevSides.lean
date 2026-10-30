-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevSides.lean: the key sides of a lookup whose keys come in m parts: m product trees
in a row, each from the claim on its own root, by recursion on the list of parts.

sideA | sidesA carry the library's honest side as data; side_good | sides_good state of them the
library's GoodAt WHOLE
  (acc, keeps, prBad, cover, prCov, same beside know); no masked clause is stated.

  `KeyBase`     what all key sides of a lookup share, read off the state with which the first side
                is entered: the challenge lam; the names J of the entries.
  `KeyPart B`   one part: 2^(v' + 1) keys; its keys; the masked claim on its root (form fK, target
                tK); the places of its levels' own mask entries (wK, cK: letters; that the last
                level's two lie in another message is a value of cK); the order oK l in which level
                l binds its l variables.
  `KeyPart.sideA`  one side, entered at any type X of states with a reading pr of the base state.
  `SidesSt p ps X pr`  the type of states behind the sides of p :: ps: a family by recursion on the
                parts. `sidesA`: the sides in a row.
  `sides_good`  for every riding R0 and all Ψ, ΨR: from «Ψ, and every part's root claim holds» to
                «Ψ at the state of entry, and for each part its levels' rows hold and its masked
                claim
                on the extension of its own keys at its own point holds» (`sidesOut`): `BkA.Good`.
  `sides_know`  the clause on knowledge soundness alone, of the reduction and its errors.
  `sides_rounds`  the number of rounds: the sum over the parts of the sum over l ≤ v' of l + 4.
  `side_sg`     level l of a part's tree has the order p.oK l.
Conditions: none beyond the letters' types (a part has at least two keys; there is a first part).
Not claimed: what the orders are; that the roots' claims come from earlier steps; anything on the
table; that the places wK, cK are pairwise different.
The side itself, its state of entry, rows and end claim: after E3SegK.

-/
import Cb.Ld.LdLkpSegK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Iop IOR Hiop Prob

noncomputable section

/-- What all key sides of one lookup share. -/
structure KeyBase (E : Type) [Field E] [Fintype E] where
  /-- the states with which the first side is entered -/
  X0 : Type
  St : Type
  st : X0 → St
  lam : X0 → E
  J : Type
  [finJ : Fintype J]

attribute [instance] KeyBase.finJ

variable {E : Type} [Field E] [Fintype E]

/-- One part of the keys. -/
structure KeyPart (B : KeyBase E) where
  /-- the part has 2^(v' + 1) keys -/
  v' : ℕ
  key : B.St → (B.J → E) → ℕ → E
  /-- the masked claim on the part's root: its form and its target -/
  fK : B.X0 → B.J → E
  tK : B.X0 → E
  /-- the places of the levels' own mask entries -/
  wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → B.J
  cK : ℕ → Bool → B.J
  /-- round j of level l binds variable oK l j -/
  oK : (l : ℕ) → Equiv.Perm (Fin (0 + l))

/-- `BkA.Good` between joints of the form cj does not see how their clauses are bracketed. -/
theorem good_congr {Kc M X₁ X₂ St' Wp J : Type} {Ex : ExtSpec} (b : BkA Kc M X₁ X₂ Ex Wp)
    (R0 : Rels Kc St' Ex (M × Wp)) (msg : M → J → E) (q₁ : X₁ → St') (q₂ : X₂ → St')
    (Φ ΦR Φ' ΦR' : X₁ → (J → E) → Prop) (Θ ΘR Θ' ΘR' : X₂ → (J → E) → Prop)
    (h₁ : ∀ x m, Φ x m ↔ Φ' x m) (h₂ : ∀ x m, ΦR x m ↔ ΦR' x m)
    (h₃ : ∀ x m, Θ x m ↔ Θ' x m) (h₄ : ∀ x m, ΘR x m ↔ ΘR' x m)
    (g : b.Good (cj R0 msg q₁ Φ ΦR) (cj R0 msg q₂ Θ ΘR)) :
    b.Good (cj R0 msg q₁ Φ' ΦR') (cj R0 msg q₂ Θ' ΘR') := by
  rw [← ldLkpK_congr E Kc St' M Wp J X₁ Ex R0 msg q₁ Φ ΦR Φ' ΦR' h₁ h₂,
    ← ldLkpK_congr E Kc St' M Wp J X₂ Ex R0 msg q₂ Θ ΘR Θ' ΘR' h₃ h₄]
  exact g

/-- Whether all rows of a list hold does not see their order. -/
theorem rowsHold_rev {J : Type} [Fintype J] (l : List (Row E J)) (m : J → E) :
    RowsHold l.reverse m ↔ RowsHold l m :=
  ⟨fun h r hr => h r (List.mem_reverse.2 hr), fun h r hr => h r (List.mem_reverse.1 hr)⟩

namespace KeyPart
variable {B : KeyBase E} (p : KeyPart B) (X : Type) (pr : X → B.X0)

/-- The part as an instance of the library's record with orders, entered at states X. The table's
fields are idle here. -/
def inst : LkInst E where
  X := X
  St := B.St
  st := fun x => B.st (pr x)
  lam := fun x => B.lam (pr x)
  J := B.J
  v := p.v' + 1
  d := 0
  w := 0
  key := p.key
  tab := fun _ _ => 0
  bAt := fun _ _ => p.cK 0 false
  fK := fun x => p.fK (pr x)
  formT := fun _ _ _ => 0
  wK := p.wK
  cK := p.cK
  wT := fun _ _ => p.cK 0 false
  cT := p.cK
  oK := p.oK
  oT := fun _ => Equiv.refl _

/-- the part's tree -/
abbrev tree : TreeP E := ((p.inst X pr).setV (p.v' + 1)).DK

/-- level l of the part's tree binds its variables in the order p.oK l -/
theorem side_sg (l : ℕ) : (p.tree X pr).sg l = p.oK l := rfl

/-- the states behind the part's side -/
abbrev SideSt : Type := E × ((p.tree X pr).lv (p.v' + 1)).T.St

/-- the state with which the side was entered -/
def old (x : p.SideSt X pr) : X := oldK (p.inst X pr) p.v' x

/-- the reading of the base state behind the side -/
def prN : p.SideSt X pr → B.X0 := fun x => pr (p.old X pr x)

/-- the claim on the part's root -/
def RootHolds (x0 : B.X0) (m : B.J → E) : Prop :=
  keyProd (p.v' + 1) (p.key (B.st x0) m) (B.lam x0) + ∑ j, p.fK x0 j * m j = p.tK x0

/-- the masked claim on the part's keys that leaves the side, and the rows of its levels -/
def cl (x : p.SideSt X pr) : MCl E B.J := ((p.inst X pr).setV (p.v' + 1)).topCl x
def rows (x : p.SideSt X pr) : List (Row E B.J) := (rowsK (p.inst X pr) p.v' x).reverse

def OutHolds (x : p.SideSt X pr) (m : B.J → E) : Prop :=
  RowsHold (p.rows X pr x) m ∧ (p.cl X pr x).Holds (p.v' + 1) (p.key (B.st (p.prN X pr x)) m) m

/-- One key side. -/
def sideA (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → B.J → E) : BkA Kc M X (p.SideSt X pr) Ex Wp :=
  segK (p.inst X pr) p.v' (fun x => p.tK (pr x)) Ex M Wp Kc msg

theorem side_good (Ex : ExtSpec) (Kc St' M Wp : Type) (R0 : Rels Kc St' Ex (M × Wp)) (msg : M →
    B.J → E)
    (q : X → St') (Ψ ΨR : X → (B.J → E) → Prop) :
    (p.sideA X pr Ex M Wp Kc msg).Good
      (cj R0 msg q (fun x m => Ψ x m ∧ p.RootHolds (pr x) m) fun x m => ΨR x m ∧ p.RootHolds (pr x)
          m)
      (cj R0 msg (fun x => q (p.old X pr x)) (fun x m => Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m)
        fun x m => ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) :=
  good_congr (p.sideA X pr Ex M Wp Kc msg) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun _ _ => ⟨fun h => ⟨h.1.1, (rowsHold_rev _ _).2 h.1.2, h.2⟩,
      fun h => ⟨⟨h.1, (rowsHold_rev _ _).1 h.2.1⟩, h.2.2⟩⟩)
    (fun _ _ => ⟨fun h => ⟨h.1.1, (rowsHold_rev _ _).2 h.1.2, h.2⟩,
      fun h => ⟨⟨h.1, (rowsHold_rev _ _).1 h.2.1⟩, h.2.2⟩⟩)
    (ldLkpSegK_good E (p.inst X pr) p.v' (fun x => p.tK (pr x)) Ex Kc St' M Wp R0 msg q Ψ ΨR)

theorem side_rounds (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → B.J → E) :
    (p.sideA X pr Ex M Wp Kc msg).R.shape.length = ∑ l ∈ Finset.range (p.v' + 1), (0 + l + 3 + 1) :=
  ldLkpSegK_rounds E (p.inst X pr) p.v' (fun x => p.tK (pr x)) Ex M Wp Kc msg

end KeyPart

variable {B : KeyBase E}

/-- The states behind the sides of the parts p :: ps: a family by recursion on the parts. -/
def SidesSt : KeyPart B → List (KeyPart B) → (X : Type) → (X → B.X0) → Type
  | p, [], X, pr => p.SideSt X pr
  | p, r :: ps, X, pr => SidesSt r ps (p.SideSt X pr) (p.prN X pr)

/-- the state with which the first side was entered -/
def sidesOld : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) → SidesSt p
    ps X pr → X
  | p, [], X, pr, x => p.old X pr x
  | p, r :: ps, X, pr, x => p.old X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x)

/-- what has been reached behind all sides: for each part its rows and its own masked claim -/
def sidesOut : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) →
    SidesSt p ps X pr → (B.J → E) → Prop
  | p, [], X, pr, x, m => p.OutHolds X pr x m
  | p, r :: ps, X, pr, x, m =>
    p.OutHolds X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x) m ∧
      sidesOut r ps (p.SideSt X pr) (p.prN X pr) x m

/-- the claims on the roots of a list of parts -/
def rootsHold : List (KeyPart B) → B.X0 → (B.J → E) → Prop
  | [], _, _ => True
  | r :: rs, x, m => r.RootHolds x m ∧ rootsHold rs x m

/-- The key sides of the parts p :: ps, one after the other. -/
def sidesA (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → B.J → E) :
    (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) →
      BkA Kc M X (SidesSt p ps X pr) Ex Wp
  | p, [], X, pr => p.sideA X pr Ex M Wp Kc msg
  | p, r :: ps, X, pr =>
    (p.sideA X pr Ex M Wp Kc msg).seq (sidesA Ex M Wp Kc msg r ps (p.SideSt X pr) (p.prN X pr))

/-- m key sides in a row. -/
theorem sides_good (Ex : ExtSpec) (Kc St' M Wp : Type) (R0 : Rels Kc St' Ex (M × Wp)) (msg : M →
    B.J → E) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0) (q : X → St')
      (Ψ ΨR : X → (B.J → E) → Prop),
      (sidesA Ex M Wp Kc msg p ps X pr).Good
        (cj R0 msg q (fun x m => Ψ x m ∧ rootsHold (p :: ps) (pr x) m)
          fun x m => ΨR x m ∧ rootsHold (p :: ps) (pr x) m)
        (cj R0 msg (fun x => q (sidesOld p ps X pr x))
          (fun x m => Ψ (sidesOld p ps X pr x) m ∧ sidesOut p ps X pr x m)
          fun x m => ΨR (sidesOld p ps X pr x) m ∧ sidesOut p ps X pr x m)
  | [], p, X, pr, q, Ψ, ΨR =>
    good_congr (p.sideA X pr Ex M Wp Kc msg) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
      (fun _ _ => ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩)
      (fun _ _ => ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩)
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (p.side_good X pr Ex Kc St' M Wp R0 msg q Ψ ΨR)
  | r :: ps, p, X, pr, q, Ψ, ΨR => by
    have g1 : (p.sideA X pr Ex M Wp Kc msg).Good
        (cj R0 msg q (fun x m => Ψ x m ∧ rootsHold (p :: r :: ps) (pr x) m)
          fun x m => ΨR x m ∧ rootsHold (p :: r :: ps) (pr x) m)
        (cj R0 msg (fun x => q (p.old X pr x))
          (fun x m => (Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
          fun x m => (ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m) :=
      good_congr (p.sideA X pr Ex M Wp Kc msg) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
        (fun _ _ => ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩)
        (fun _ _ => ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩)
        (fun _ _ => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)
        (fun _ _ => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)
        (p.side_good X pr Ex Kc St' M Wp R0 msg q (fun x m => Ψ x m ∧ rootsHold (r :: ps) (pr x) m)
          fun x m => ΨR x m ∧ rootsHold (r :: ps) (pr x) m)
    have g2 : (sidesA Ex M Wp Kc msg r ps (p.SideSt X pr) (p.prN X pr)).Good
        (cj R0 msg (fun x => q (p.old X pr x))
          (fun x m => (Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
          fun x m => (ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
        (cj R0 msg (fun x => q (sidesOld p (r :: ps) X pr x))
          (fun x m => Ψ (sidesOld p (r :: ps) X pr x) m ∧ sidesOut p (r :: ps) X pr x m)
          fun x m => ΨR (sidesOld p (r :: ps) X pr x) m ∧ sidesOut p (r :: ps) X pr x m) :=
      good_congr (sidesA Ex M Wp Kc msg r ps (p.SideSt X pr) (p.prN X pr)) R0 msg
        (fun x => q (p.old X pr x)) (fun x => q (sidesOld p (r :: ps) X pr x)) _ _ _ _ _ _ _ _
        (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => and_assoc) (fun _ _ => and_assoc)
        (sides_good Ex Kc St' M Wp R0 msg ps r (p.SideSt X pr) (p.prN X pr) (fun x => q (p.old X pr
            x))
          (fun x m => Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m)
          fun x m => ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m)
    exact goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ _ _ _ (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ g1 g2 fun _ _ _ _ _ _ _ => rfl

/-- Knowledge soundness alone, for each fixed tuple of messages; the identity extracts. It names the
reduction and its errors, no honest side. -/
theorem sides_know (Ex : ExtSpec) (Kc St' M Wp : Type) (R0 : Rels Kc St' Ex (M × Wp)) (msg : M →
    B.J → E)
    (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0) (q : X → St')
    (ΨR : X → (B.J → E) → Prop) (m : M) :
    (sidesA Ex M Wp Kc msg p ps X pr).R.red.Know (fun a => R0.on (q a.1, a.2))
      (fun a wp => R0.relR (q a.1, a.2) (m, wp) ∧ ΨR a.1 (msg m) ∧ rootsHold (p :: ps) (pr a.1) (msg
          m))
      (fun b wp => R0.relR (q (sidesOld p ps X pr b.1), b.2) (m, wp) ∧
        ΨR (sidesOld p ps X pr b.1) (msg m) ∧ sidesOut p ps X pr b.1 (msg m))
      (fun _ _ wp => wp) (sidesA Ex M Wp Kc msg p ps X pr).P.err :=
  GoodAt.know (sides_good Ex Kc St' M Wp R0 msg ps p X pr q ΨR ΨR) m

/-- The rounds of m key sides. -/
theorem sides_rounds (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → B.J → E) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
      (sidesA Ex M Wp Kc msg p ps X pr).R.shape.length =
        ((p :: ps).map fun r => ∑ l ∈ Finset.range (r.v' + 1), (0 + l + 3 + 1)).sum
  | [], p, X, pr => by
    rw [List.map_singleton, List.sum_singleton]
    exact p.side_rounds X pr Ex M Wp Kc msg
  | r :: ps, p, X, pr => by
    have e : (sidesA Ex M Wp Kc msg p (r :: ps) X pr).R.shape =
        (p.sideA X pr Ex M Wp Kc msg).R.shape ++
          (sidesA Ex M Wp Kc msg r ps (p.SideSt X pr) (p.prN X pr)).R.shape := rfl
    rw [e, List.length_append, p.side_rounds X pr Ex M Wp Kc msg,
      sides_rounds Ex M Wp Kc msg ps r (p.SideSt X pr) (p.prN X pr)]
    simp only [List.map_cons, List.sum_cons]

end
end Lk6

#print axioms Lk6.sides_good
#print axioms Lk6.sides_know
#print axioms Lk6.sides_rounds
