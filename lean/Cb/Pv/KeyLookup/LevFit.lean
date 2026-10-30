-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevFit.lean: the key sides and the table's tree of a lookup with parts, between the
joints of Letters.lean, as blocks without an honest side over its one flat state.

  `LevPl A`     the places of the own mask entries of the key levels (by part and level) and of the
                table's levels: letters.
  `Dat.part L i`  part i: 2^(v i) keys; the claim on its root is x.roots i; its orders are
                `ordKey A.order (v i)`.
  `Dat.keysK L SK`  the m key sides in a row, then a step without rounds back into the flat state:
                cls i := part i's claim; the rows appended.
  `Dat.keys_know`  Know from `Joined` to `Table · · 0`.
  `Dat.tabT L`  the table's tree: mu low variables, d levels, leaf number c := A.leaf (row c / 2^mu)
                (plane c % 2^mu); orders `ordTab A.mu`.
  `Dat.tableK L SK`, `Dat.table_know`  Know from `Table · · 0` to `Table · · d`.
  `keys_lt_lib`, `table_lt_lib`  the conditions on the letter hold at the library's own verifier.
Conditions: 1 ≤ m; 1 ≤ v i for i < m; 1 ≤ d: all three are clauses of `Pub.Adm`. (A tree of no level
is no block here. `Lkp.Public.ok` has no floor for d: its `sizesOK`, OnBytes/Iop/Lkp.lean, asks
S.d < 64 alone; the one caller of that verifier asks 1 ≤ d: `lookupOk`, OnBytes/Key/Ranges.lean.)
And on the sumcheck's letter: `SidesLt`, `LtS`.
Not claimed: anything on the exact side (Mu rides unread); the inner joints `Keys k` and `Table l`
for 0 < l < d. `keys_know` does not ask the clause `Adm.order`: where the named variables are no
lawful beginning the last level falls back to the reversal, while the verifier in
OnBytes/Iop/Lkp.lean refuses.

-/
import Cb.Pv.KeyLookup.LevK
import Cb.Pv.KeyLookup.LevOut
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob Finset

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- The places of the own mask entries of the key levels and of the table's levels. -/
structure LevPl (A : Dat E) where
  wK : (i l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → A.J
  cK : ℕ → ℕ → Bool → A.J
  wT : (l : ℕ) → PIdx (List.replicate (A.mu + l) (pfCube E 2) ++ [pDummy E 2]) → A.J
  cT : ℕ → Bool → A.J

theorem rowsHold_app {N : Type} [Fintype N] (a b : List (Row E N)) (m : N → E) :
    RowsHold (a ++ b) m ↔ RowsHold a m ∧ RowsHold b m :=
  ⟨fun h => ⟨fun r hr => h r (List.mem_append_left _ hr), fun r hr => h r (List.mem_append_right _
      hr)⟩,
    fun h r hr => (List.mem_append.1 hr).elim (h.1 r) (h.2 r)⟩

theorem mleN_congr {k k' : ℕ} (h : k = k') (f : ℕ → E) (pt : ℕ → E) : mleN k f pt = mleN k' f pt :=
    by
  subst h; rfl

namespace Dat
variable (A : Dat E) (L : LevPl A) {Ex : ExtSpec}

/-! ### the key sides -/

def kb : KeyBase E where
  X0 := A.XS
  St := A.St
  st := fun x => x.st
  lam := fun x => x.al
  J := A.J

def part (i : ℕ) : KeyPart A.kb where
  v' := A.v i - 1
  key := fun st μ => A.key st μ i
  fK := fun x => (x.roots i).mf
  tK := fun x => (x.roots i).tg
  wK := L.wK i
  cK := L.cK i
  oK := ordKey A.order (A.v i - 1 + 1)

def tailP : List (KeyPart A.kb) := (List.range (A.m - 1)).map fun i => A.part L (i + 1)

theorem parts_len (hm : 1 ≤ A.m) : (A.part L 0 :: A.tailP L).length = A.m := by
  unfold tailP
  rw [List.length_cons, List.length_map, List.length_range]
  omega

theorem parts_get (i : ℕ) (h : i < (A.part L 0 :: A.tailP L).length) :
    (A.part L 0 :: A.tailP L)[i] = A.part L i := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold tailP
    rw [List.getElem_cons_succ, List.getElem_map, List.getElem_range]

abbrev KSt : Type := SidesSt (A.part L 0) (A.tailP L) A.XS id

def oldK (x : A.KSt L) : A.XS := sidesOld (A.part L 0) (A.tailP L) A.XS id x

/-- the rows of all key levels -/
def rowsK (x : A.KSt L) : List (Row E A.J) := sidesRows (A.part L 0) (A.tailP L) A.XS id x

/-- back into the flat state -/
def backK (x : A.KSt L) : A.XS :=
  { A.oldK L x with
    cls := fun i => (sidesCl (A.part L 0) (A.tailP L) A.XS id x).getD i ⟨0, 0, 0⟩
    rows := (A.oldK L x).rows ++ A.rowsK L x }

/-- The m key sides: the verifier's side and its errors, over the flat state. -/
def keysK (SK : PscLtK E Ex) : BkK A.XS A.XS Ex :=
  (sidesK SK (A.part L 0) (A.tailP L) A.XS id).postM (A.backK L)

theorem root_iff (i : ℕ) (hv : 1 ≤ A.v i) (x : A.XS) (μ : A.J → E) :
    (A.part L i).RootHolds x μ ↔ (x.roots i).Holds (A.root x.st μ x.al i) μ := by
  have e : A.v i - 1 + 1 = A.v i := Nat.sub_add_cancel hv
  show keyProd (A.v i - 1 + 1) (A.key x.st μ i) x.al + ∑ j, (x.roots i).mf j * μ j = (x.roots
      i).tg ↔
    keyProd (A.v i) (A.key x.st μ i) x.al + ∑ j, (x.roots i).mf j * μ j = (x.roots i).tg
  rw [e]

theorem roots_iff (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) (x : A.XS) (μ : A.J → E) :
    rootsHold (A.part L 0 :: A.tailP L) x μ ↔ A.AllRoots x μ := by
  rw [rootsHold_iff]
  constructor
  · intro h i hi
    have h' := h i (by rw [A.parts_len L hm]; exact hi)
    rw [A.parts_get L i] at h'
    exact (A.root_iff L i (hv i hi) x μ).1 h'
  · intro h i hi
    have hi' : i < A.m := by rw [A.parts_len L hm] at hi; exact hi
    rw [A.parts_get L i]
    exact (A.root_iff L i (hv i hi') x μ).2 (h i hi')

theorem cls_iff (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) (x : A.KSt L) (μ : A.J → E) :
    clsHold (A.part L 0 :: A.tailP L) (sidesCl (A.part L 0) (A.tailP L) A.XS id x) (A.oldK L x) μ ↔
      A.AllCls (A.backK L x) μ := by
  have hl : (sidesCl (A.part L 0) (A.tailP L) A.XS id x).length = (A.part L 0 :: A.tailP
      L).length :=
    sidesCl_length (A.tailP L) (A.part L 0) A.XS id x
  rw [clsHold_iff _ _ _ _ hl]
  have key : ∀ (i : ℕ) (hi : i < A.m) (h : i < (A.part L 0 :: A.tailP L).length)
      (h' : i < (sidesCl (A.part L 0) (A.tailP L) A.XS id x).length),
      ((sidesCl (A.part L 0) (A.tailP L) A.XS id x)[i].Holds ((A.part L 0 :: A.tailP L)[i].v' + 1)
        ((A.part L 0 :: A.tailP L)[i].key (A.kb.st (A.oldK L x)) μ) μ ↔
      ((A.backK L x).cls i).Holds (A.v i) (A.key (A.backK L x).st μ i) μ) := by
    intro i hi h h'
    have e : A.v i - 1 + 1 = A.v i := Nat.sub_add_cancel (hv i hi)
    have ec : (A.backK L x).cls i = (sidesCl (A.part L 0) (A.tailP L) A.XS id x)[i] :=
      List.getD_eq_getElem _ _ h'
    rw [A.parts_get L i h, ec]
    show (sidesCl (A.part L 0) (A.tailP L) A.XS id x)[i].Holds (A.v i - 1 + 1)
        (A.key (A.oldK L x).st μ i) μ ↔ _
    rw [e]
    exact Iff.rfl
  constructor
  · intro h i hi
    have h1 : i < (A.part L 0 :: A.tailP L).length := by rw [A.parts_len L hm]; exact hi
    exact (key i hi h1 (hl ▸ h1)).1 (h i h1 (hl ▸ h1))
  · intro h i h1 h2
    have hi : i < A.m := by rw [A.parts_len L hm] at h1; exact h1
    exact (key i hi h1 h2).2 (h i hi)

/-- what `Table · · 0` says of the state that is handed back -/
theorem table0_back (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) (x : A.KSt L) (μ : A.J → E) :
    A.Table (A.backK L x) μ 0 ↔
      (A.Side (A.oldK L x) μ ∧ A.TopAt (A.oldK L x) μ 0) ∧
        sidesOut (A.part L 0) (A.tailP L) A.XS id x μ := by
  rw [sidesOut_iff]
  have hc := A.cls_iff L hm hv x μ
  have hr : RowsHold (A.backK L x).rows μ ↔
      RowsHold (A.oldK L x).rows μ ∧ RowsHold (A.rowsK L x) μ :=
    rowsHold_app (A.oldK L x).rows (A.rowsK L x) μ
  constructor
  · rintro ⟨⟨hb, hrw⟩, hcl, ht⟩
    exact ⟨⟨⟨hb, (hr.1 hrw).1⟩, ht⟩, (hr.1 hrw).2, hc.2 hcl⟩
  · rintro ⟨⟨⟨hb, h1⟩, ht⟩, h2, hcl⟩
    exact ⟨⟨hb, hr.2 ⟨h1, h2⟩⟩, hc.1 hcl, ht⟩

theorem keys_know (SK : PscLtK E Ex) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M →
    A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i)
    (hL : SidesLt (B := A.kb) SK Wp Kc msg (A.part L 0) (A.tailP L) A.XS id) :
    (A.keysK L SK).Know (A.jt R0 msg Mu A.Joined) (A.jt R0 msg Mu fun x μ => A.Table x μ 0) := by
  have g := sidesK_know (B := A.kb) SK Kc A.St M Wp R0 msg (A.tailP L) (A.part L 0) A.XS id
    (fun x => x.st) (fun x μ => (A.Side x μ ∧ A.TopAt x μ 0) ∧ Mu x.st μ)
    (fun x μ => A.Side x μ ∧ A.TopAt x μ 0) hL
  have g' := know_congr _ R0 msg (fun x : A.XS => x.st) _ _ _
    (fun x μ => A.Joined x μ ∧ Mu x.st μ) A.Joined _ _ _ _
    (fun x μ => ⟨fun h => ⟨⟨h.1.1.1, (A.roots_iff L hm hv x μ).1 h.2, h.1.1.2⟩, h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1, h.1.2.2⟩, h.2⟩, (A.roots_iff L hm hv x μ).2 h.1.2.1⟩⟩)
    (fun x μ => ⟨fun h => ⟨h.1.1, (A.roots_iff L hm hv x μ).1 h.2, h.1.2⟩,
      fun h => ⟨⟨h.1, h.2.2⟩, (A.roots_iff L hm hv x μ).2 h.2.1⟩⟩)
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) g
  refine know_postM (A.backK L) g' (fun _ _ h => h) ?_
  intro x y w _ h
  exact ⟨h.1, (A.table0_back L hm hv x (msg w.1)).1 h.2⟩

theorem keys_lt_lib (Kc M Wp : Type) (msg : M → A.J → E) :
    SidesLt (B := A.kb) (PscLtK.lib E Ex) Wp Kc msg (A.part L 0) (A.tailP L) A.XS id :=
  sidesLt_lib (B := A.kb) Wp Kc msg (A.tailP L) (A.part L 0) A.XS id

/-! ### the table's tree -/

def tabT : ProdT E where
  X := A.XS
  J := A.J
  g := A.mu
  n' := A.d - 1
  leaf := fun x μ c => A.leaf x.st μ x.al (c / 2 ^ A.mu) (c % 2 ^ A.mu)
  pt0 := fun x i => x.pt i
  f0 := fun x => x.top.mf
  t0 := fun x => x.top.tg
  wAt := L.wT
  cAt := L.cT
  sg := ordTab A.mu

/-- the rows of the table's levels -/
def rowsT (x : (A.tabT L).TopSt) : List (Row E A.J) := (A.tabT L).rows x

/-- back into the flat state -/
def backT (x : (A.tabT L).TopSt) : A.XS :=
  { (A.tabT L).old x with
    top := ⟨(A.tabT L).form x, x.1⟩
    pt := fun i => if h : i < A.mu + (A.d - 1 + 1) then (A.tabT L).pnt x ⟨i, h⟩ else 0
    rows := ((A.tabT L).old x).rows ++ A.rowsT L x }

def tableK (SK : PscLtK E Ex) : BkK A.XS A.XS Ex := ((A.tabT L).segK SK).postM (A.backT L)

theorem tab_in (hd : 1 ≤ A.d) (x : A.XS) (μ : A.J → E) : (A.tabT L).InHolds x μ ↔ A.TopAt x μ 0 :=
    by
  have e : A.d - 1 + 1 = A.d := Nat.sub_add_cancel hd
  have hU : cubeLvl A.mu (A.d - 1 + 1)
        (fun c => A.leaf x.st μ x.al (c / 2 ^ A.mu) (c % 2 ^ A.mu)) 0 =
      fun b : Fin (A.mu + 0) → Bool => A.tabU x.st μ x.al 0 (numLE b) := by
    funext b
    have hb : numLE b < 2 ^ A.mu := ldLkpNum_lt (A.mu + 0) b
    rw [ldLkpNum_root, e]
    unfold Dat.tabU
    rw [Nat.sub_zero]
    refine Finset.prod_congr rfl fun z _ => ?_
    have h1 : (z * 2 ^ A.mu + numLE b) / 2 ^ A.mu = z := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb,
          Nat.zero_add]
    have h2 : (z * 2 ^ A.mu + numLE b) % 2 ^ A.mu = numLE b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    rw [h1, h2, Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb, pow_zero, Nat.one_mul, Nat.zero_add]
  show Alg.mle (cubeLvl A.mu (A.d - 1 + 1)
        (fun c => A.leaf x.st μ x.al (c / 2 ^ A.mu) (c % 2 ^ A.mu)) 0) (fun i : Fin (A.mu + 0) =>
            x.pt i) +
      ∑ j, x.top.mf j * μ j = x.top.tg ↔ _
  rw [hU]
  exact Iff.rfl

theorem tab_top (hd : 1 ≤ A.d) (x : (A.tabT L).TopSt) (μ : A.J → E) :
    A.TopAt (A.backT L x) μ A.d ↔ (A.tabT L).TopHolds x μ := by
  have e : A.mu + A.d = A.mu + (A.d - 1 + 1) := by rw [Nat.sub_add_cancel hd]
  have hf : A.tabU ((A.tabT L).old x).st μ ((A.tabT L).old x).al A.d =
      fun n => A.leaf ((A.tabT L).old x).st μ ((A.tabT L).old x).al (n / 2 ^ A.mu) (n % 2 ^ A.mu) :=
          by
    funext n
    unfold Dat.tabU
    rw [Nat.sub_self, pow_zero, Finset.range_one, Finset.prod_singleton, Nat.mul_zero, Nat.add_zero]
  have hp : (fun i : Fin (A.mu + (A.d - 1 + 1)) => (A.backT L x).pt i) = (A.tabT L).pnt x := by
    funext i
    show (if h : i.1 < A.mu + (A.d - 1 + 1) then (A.tabT L).pnt x ⟨i.1, h⟩ else 0) = _
    rw [dif_pos i.2]
    rfl
  show mleN (A.mu + A.d) (A.tabU ((A.tabT L).old x).st μ ((A.tabT L).old x).al A.d) (A.backT L
      x).pt +
      ∑ j, (A.tabT L).form x j * μ j = x.1 ↔ _
  rw [mleN_congr e, hf]
  unfold mleN
  rw [hp]
  exact Iff.rfl

theorem table_know (SK : PscLtK E Ex) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M →
    A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hd : 1 ≤ A.d)
    (hL : LtS (A.tabT L).tree SK Wp Kc msg (A.tabT L).n') :
    (A.tableK L SK).Know (A.jt R0 msg Mu fun x μ => A.Table x μ 0)
      (A.jt R0 msg Mu fun x μ => A.Table x μ A.d) := by
  have g := (A.tabT L).segK_know SK Kc A.St M Wp R0 msg (fun x => x.st)
    (fun x μ => (A.Side x μ ∧ A.AllCls x μ) ∧ Mu x.st μ) (fun x μ => A.Side x μ ∧ A.AllCls x μ) hL
  have g' := know_congr _ R0 msg (fun x : A.XS => x.st) _ _ _
    (fun x μ => A.Table x μ 0 ∧ Mu x.st μ) (fun x μ => A.Table x μ 0) _ _ _ _
    (fun x μ => ⟨fun h => ⟨⟨h.1.1.1, h.1.1.2, (A.tab_in L hd x μ).1 h.2⟩, h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, (A.tab_in L hd x μ).2 h.1.2.2⟩⟩)
    (fun x μ => ⟨fun h => ⟨h.1.1, h.1.2, (A.tab_in L hd x μ).1 h.2⟩,
      fun h => ⟨⟨h.1, h.2.1⟩, (A.tab_in L hd x μ).2 h.2.2⟩⟩)
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) g
  refine know_postM (A.backT L) g' (fun _ _ h => h) ?_
  intro x y w _ h
  obtain ⟨hR, ⟨hb, hrw⟩, hcl, ht⟩ := h
  have hr := (rowsHold_app ((A.tabT L).old x).rows (A.rowsT L x) (msg w.1)).1 hrw
  exact ⟨hR, ⟨⟨⟨hb, hr.1⟩, hcl⟩, hr.2⟩, (A.tab_top L hd x (msg w.1)).1 ht⟩

theorem table_lt_lib (Kc M Wp : Type) (msg : M → A.J → E) :
    LtS (A.tabT L).tree (PscLtK.lib E Ex) Wp Kc msg (A.tabT L).n' :=
  lt_lib (A.tabT L).tree Wp Kc msg (A.tabT L).n'

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_know
#print axioms Lk6.Dat.table_know
#print axioms Lk6.Dat.keys_lt_lib
#print axioms Lk6.Dat.table_lt_lib
