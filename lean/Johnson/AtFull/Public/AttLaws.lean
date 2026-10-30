-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AttLaws.lean: THE ATTENTION's GENERAL LAWS AND ITS CERTIFICATE attB, ending in
  config_of_check.
RE-CUT BY PROGRAM out of an earlier working file of this project, which is not in this repository
  (sha256 9ec468ab…), its lines 428-727: NO LETTER OF LEAN TURNS but the prefix of three calls: the
  forest's laws shape_eq | ask_eq
are Johnson/Unfolds/ShapeEq.lean's (Johnson.Unfolds.…), where that working file has them under
  L10ShapeEq.
The recursion limit is raised in this file (maxRecDepth 1000000).
Nothing on soundness.
-/
import Johnson.AtFull.Public.Twins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial

/-- A test at what a maker returns; false where it refuses. -/
def onOk {ε α : Type} (x : Except ε α) (f : α → Bool) : Bool :=
  match x with
  | .ok a => f a
  | .error _ => false

/-- Two closed inequalities from which every row of the table of kind KFD is below the prime, if the
  exponentials
are at most M. -/
def kfdB (M : Nat) (d : Attention.ShD) (sh k : Nat) : Bool :=
  decide (2 ^ k * 2 ^ sh + M * 2 ^ 33 < 18446744069414584321) &&
    decide (d.C + d.rho * 2 ^ k + d.rho / 2 + 2 ^ 32 < 18446744069414584321)

/-- The test on one call of a shape: callAsk's tests on the numbers, and kfdB at a call of kind KFD.
  -/
def askAt (M : Nat) (cf : Attention.Cfg) (A : Attention.Shape) (k : Attention.ACall) : Bool :=
  onOk (Model.Forest.callAskNoTab k.call) (fun _ => true) &&
    (if k.kind = .kfd then
      kfdB M (Attention.shdOf A.Tt.size (2 ^ cf.ldh * Model.clamp * Model.clamp) k.sh) k.sh cf.kFD
    else true)

/-- The test on all calls of the shape that the twin returns. -/
def asksB (tt : Option (Array Nat)) (M : Nat) (cf : Attention.Cfg) : Bool :=
  onOk (Attention.shapeS tt cf) fun A => A.calls.toList.all (askAt M cf A)

/-- **The certificate for the attention's configuration**: the lines callA are read; at each group
  fill returns a
configuration with S = 12, rx = 8 at which asksB accepts. -/
def attB (tt : Option (Array Nat)) (M : Nat) (P : Model.PolScan) (y : Model.Layer.Lay)
    (s : Model.Layer.Scales) : Bool :=
  onOk (Attention.readLines P.polCallsA) fun lines => (List.range y.NGr).all fun g =>
    onOk (Attention.fill P y s lines g) fun cf => cf.S == 12 && cf.rx == 8 && asksB tt M cf

end OnBytes.Road.K4.Trial

namespace OnBytes.Road.K4.Trial.AttLaws
open OnBytes OnBytes.Model OnBytes.Attention
open OnBytes.Road.L5 (bind_ok refuse_ok mapM_mem calls_of_shape layCall_kind smOf shaped_of_shape
    refL
  expTable_ref)
open VerifiableInference.PlanWritten.Attention (configO configS)

/-! ## Tools -/

theorem onOk_ok {ε α : Type} {x : Except ε α} {f : α → Bool} {a : α} (h : onOk x f = true)
    (e : x = .ok a) : f a = true := by
  subst e
  exact h

theorem onOk_ex {ε α : Type} {x : Except ε α} {f : α → Bool} (h : onOk x f = true) :
    ∃ a, x = .ok a ∧ f a = true := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => exact absurd h (by simp [onOk])

/-- Two runs that go on alike wherever the first step returns are equal. -/
theorem bind_congr_ok {ε α β : Type} {x : Except ε α} {f g : α → Except ε β}
    (h : ∀ a, x = .ok a → f a = g a) : (x >>= f) = (x >>= g) := by
  cases x with
  | error e => rfl
  | ok a => exact h a rfl

theorem mapM_congr_ok {α β : Type} {f g : α → Except String β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => by rw [List.mapM_nil, List.mapM_nil]
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_congr_ok l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-! ## The twins without a sort -/

theorem placePieces_eq (cf : Cfg) (HA : Nat) (kind : Table) (sh : Nat) (segs : List Attention.Seg) :
    placePieces cf HA kind sh segs = placePiecesS cf HA kind sh segs := by
  unfold placePieces placePiecesS
  simp only [mergeSort_sortG]

theorem layCall_eq (cf : Cfg) (HA Smax : Nat) (Tt : Array Nat) :
    layCall cf HA Smax Tt = layCallS cf HA Smax Tt := by
  funext x
  unfold layCall layCallS
  simp only [placePieces_eq]
  rfl

/-- **Attention.shape is its twin without a sort, at its own table of exponentials: at all
  configurations.** -/
theorem shape_eq (cf : Cfg) : Attention.shape cf = shapeS (expTable cf.S cf.rx) cf := by
  unfold Attention.shape shapeS
  simp only [mergeSort_sortG, layCall_eq]

/-- **Where the tests on the calls return, shapeHid is its twin**: no sort, no test on a table. -/
theorem shapeHid_eq (lid : Nat) (cf : Cfg)
    (h : ∀ A, Attention.shape cf = .ok A →
      ∀ c ∈ (A.calls.map (·.call)).toList, Forest.callAsk c = .ok ()) :
    shapeHid lid cf = shapeHidS (expTable cf.S cf.rx) lid cf := by
  unfold shapeHid shapeHidS
  rw [shape_eq]
  refine bind_congr_ok fun A e => ?_
  rw [Johnson.Unfolds.shape_eq _ _ (h A ((shape_eq cf).trans e))]

/-! ## The tests on the calls' tables, by arithmetic -/

theorem okF_ofNat {n : Nat} (h : n < 18446744069414584321) : okF (UInt64.ofNat n) = true := by
  unfold okF
  have h64 : n < 2 ^ 64 := Nat.lt_trans h (by decide)
  have hp : pW.toNat = 18446744069414584321 := by decide
  rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64, hp]
  exact h

/-- A table that tableOf makes of rows below the prime passes callAsk's two tests on it. -/
theorem ask_tableOf (c : Call) (row : Nat → Nat) (ht : c.tau = tableOf c.k row)
    (hr : ∀ t, t < 2 ^ c.k → row t < 18446744069414584321) :
    Forest.callAsk c = Forest.callAskNoTab c := by
  refine Johnson.Unfolds.ask_eq c ?_ ?_
  · intro t e
    rw [ht] at e
    unfold tableOf at e
    obtain rfl := Option.some.inj e
    simp
  · intro x hx
    rw [ht] at hx
    simp [tableOf] at hx
    obtain ⟨t, h1, rfl⟩ := hx
    exact okF_ofNat (hr t h1)

theorem ask_none (c : Call) (ht : c.tau = none) : Forest.callAsk c = Forest.callAskNoTab c := by
  refine Johnson.Unfolds.ask_eq c ?_ ?_
  · intro t e
    rw [ht] at e
    cases e
  · intro x hx
    rw [ht] at hx
    simp at hx

theorem rowKR_lt (sh t : Nat) (h : t < 2 ^ 16) : rowKR sh t < 18446744069414584321 := by
  unfold rowKR
  have h' : t < 65536 := Nat.lt_of_lt_of_eq h (by decide)
  split <;> omega

theorem rowWH_lt (t : Nat) (h : t < 2 ^ 16) : rowWH t < 18446744069414584321 := by
  unfold rowWH
  have h' : t < 65536 := Nat.lt_of_lt_of_eq h (by decide)
  omega

theorem rowKFD_lt {Tt : Array Nat} {M : Nat} {d : ShD} {sh k : Nat} (hM : ∀ t, Tt.getD t 0 ≤ M)
    (hB : kfdB M d sh k = true) (t : Nat) (ht : t < 2 ^ k) :
    rowKFD Tt d sh t < 18446744069414584321 := by
  unfold kfdB at hB
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hB
  obtain ⟨h1, h2⟩ := hB
  show (if t < Tt.size then t * 2 ^ sh + Tt.getD t 0 * 2 ^ 33
    else if t < Tt.size + d.nHD then d.C - 2 ^ sh + d.rho * (t - Tt.size) + 2 ^ 32
    else d.C - 2 ^ sh + d.rho * (t - Tt.size - d.nHD) + d.rho / 2 + 2 ^ 32) < 18446744069414584321
  have hv := hM t
  generalize Tt.getD t 0 = v at hv ⊢
  have x0 : d.C - 2 ^ sh ≤ d.C := Nat.sub_le _ _
  generalize d.C - 2 ^ sh = w at x0 ⊢
  split_ifs with a b
  · have x1 : t * 2 ^ sh ≤ 2 ^ k * 2 ^ sh := Nat.mul_le_mul_right _ (Nat.le_of_lt ht)
    have x2 : v * 2 ^ 33 ≤ M * 2 ^ 33 := Nat.mul_le_mul_right _ hv
    omega
  · have x1 : d.rho * (t - Tt.size) ≤ d.rho * 2 ^ k := Nat.mul_le_mul_left _ (by omega)
    omega
  · have x1 : d.rho * (t - Tt.size - d.nHD) ≤ d.rho * 2 ^ k := Nat.mul_le_mul_left _ (by omega)
    omega

/-- **callAsk at a call that layCall has made is its tests on the numbers**, if the rows of a table
  of kind KFD are
below the prime. -/
theorem layCall_ask {cf : Cfg} {HA Sm : Nat} {Tt : Array Nat} {x : Listed} {k : ACall}
    (h : layCall cf HA Sm Tt x = .ok k)
    (hk : x.2.1 = .kfd → ∀ t, t < 2 ^ cf.kFD →
      rowKFD Tt (shdOf Tt.size Sm x.2.2.1) x.2.2.1 t < 18446744069414584321) :
    Forest.callAsk k.call = Forest.callAskNoTab k.call := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  cases kind
  · exact ask_tableOf _ (rowKR sh) rfl fun t ht => rowKR_lt sh t ht
  · exact ask_tableOf _ (rowKFD Tt (shdOf Tt.size Sm sh) sh) rfl (hk rfl)
  · exact ask_none _ rfl
  · exact ask_tableOf _ rowWH rfl fun t ht => rowWH_lt t ht

/-- callAsk returns at every call of a shape that shape has returned, if askAt accepts each. -/
theorem asks_of_shape {cf : Cfg} {A : Shape} {M : Nat} (hA : Attention.shape cf = .ok A)
    (hM : ∀ t, A.Tt.getD t 0 ≤ M) (hB : A.calls.toList.all (askAt M cf A) = true) :
    ∀ c ∈ (A.calls.map (·.call)).toList, Forest.callAsk c = .ok () := by
  intro c hc
  rw [Array.toList_map] at hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
  obtain ⟨calls, hMp, hcs, -, -⟩ := calls_of_shape hA
  have hk' : k ∈ calls := by
    rw [hcs] at hk
    simpa using hk
  obtain ⟨x, -, hx⟩ := mapM_mem _ _ _ hMp k hk'
  obtain ⟨e1, e2⟩ := layCall_kind hx
  have hb := List.all_eq_true.mp hB k hk
  unfold askAt at hb
  rw [Bool.and_eq_true] at hb
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨⟨⟩, b1, -⟩ := onOk_ex b1
  have hrow : x.2.1 = .kfd → ∀ t, t < 2 ^ cf.kFD →
      rowKFD A.Tt (shdOf A.Tt.size (smOf cf) x.2.2.1) x.2.2.1 t < 18446744069414584321 := by
    intro hkf t ht
    rw [if_pos (e1.trans hkf)] at b2
    rw [← e2]
    exact rowKFD_lt hM b2 t ht
  rw [layCall_ask hx hrow]
  exact b1

/-- **shapeHid is its twin at a given table of exponentials**, where that is the configuration's
  table, its entries are
at most M, and asksB accepts. -/
theorem hid_eq {lid : Nat} {cf : Cfg} {Tt : Array Nat} {M : Nat} (hT : expTable cf.S cf.rx = some
    Tt)
    (hM : ∀ t, Tt.getD t 0 ≤ M) (hB : asksB (some Tt) M cf = true) :
    shapeHid lid cf = shapeHidS (some Tt) lid cf := by
  have key := shapeHid_eq lid cf fun A hA => by
    have hS : shapeS (some Tt) cf = .ok A := by
      rw [← hT, ← shape_eq]
      exact hA
    have hTt : A.Tt = Tt := Option.some.inj ((shaped_of_shape hA).exp.symm.trans hT)
    have hB' := hB
    unfold asksB at hB'
    have h3 := onOk_ok hB' hS
    exact asks_of_shape hA (by rw [hTt]; exact hM) h3
  rw [hT] at key
  exact key

/-! ## The callers -/

theorem plan_eq (tt : Option (Array Nat)) (st : Settings) (i : In) (cf : Cfg)
    (h : shapeHid st.lidb cf = shapeHidS tt st.lidb cf) : plan st i cf = planS tt st i cf := by
  unfold plan planS
  rw [h]

theorem group_eq (tt : Option (Array Nat)) (P : PolScan) (y : Layer.Lay) (s : Layer.Scales)
    (mq : Nat → Nat) (lines : List Line) (g : Nat)
    (h : ∀ cf, fill P y s lines g = .ok cf →
      shapeHid P.settings.lidb cf = shapeHidS tt P.settings.lidb cf) :
    group P y s mq lines g = groupS tt P y s mq lines g := by
  unfold group groupS
  refine bind_congr_ok fun cf e => ?_
  rw [plan_eq tt _ _ _ (h cf e)]

theorem config_eq (tt : Option (Array Nat)) (o : Nat → ByteArray → ByteArray) (P : PolScan)
    (y : Layer.Lay) (s : Layer.Scales) (mq : Nat → Nat)
    (h : ∀ lines, readLines P.polCallsA = .ok lines → ∀ g ∈ List.range y.NGr, ∀ cf,
      fill P y s lines g = .ok cf → shapeHid P.settings.lidb cf = shapeHidS tt P.settings.lidb cf) :
    configO o P y s mq = configS tt o P y s mq := by
  unfold configO configS
  dsimp only
  refine bind_congr_ok fun lines e => ?_
  rw [mapM_congr_ok (f := group P y s mq lines) (g := groupS tt P y s mq lines) _
    fun g hg => group_eq tt P y s mq lines g (h lines e g hg)]
  rfl

/-! ## The table of exponentials, off the library's theorem -/

/-- The library's expTable_ref (Johnson/Road/Lane5AttExp.lean), as an equation on the array. -/
theorem expTable_W : expTable 12 8 = some refL.toArray := by
  have h := expTable_ref
  cases e : expTable 12 8 with
  | none =>
    rw [e] at h
    simp at h
  | some a =>
    rw [e] at h
    have h' : a.toList = refL := Option.some.inj h
    rw [← h', Array.toArray_toList]

/-- The library's 2,307 exponentials are at most 4096: Lean's kernel evaluates it. -/
theorem refL_small : (refL.all fun v => decide (v ≤ 4096)) = true := by decide +kernel

theorem refL_le (t : Nat) : refL.toArray.getD t 0 ≤ 4096 := by
  by_cases ht : t < refL.length
  · have e : refL.toArray.getD t 0 = refL[t] := by simp [Array.getD, ht]
    rw [e]
    exact of_decide_eq_true (List.all_eq_true.mp refL_small _ (List.getElem_mem ht))
  · have e : refL.toArray.getD t 0 = 0 := by simp [Array.getD, ht]
    rw [e]
    exact Nat.zero_le _

/-- What the certificate says of one group's configuration. -/
theorem att_at {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {lines : List Line} {g : Nat}
    (hB : attB (some refL.toArray) 4096 P y s = true) (e : readLines P.polCallsA = .ok lines)
    (hg : g ∈ List.range y.NGr) (cf : Cfg) (hcf : fill P y s lines g = .ok cf) :
    (cf.S = 12 ∧ cf.rx = 8) ∧
      shapeHid P.settings.lidb cf = shapeHidS (some refL.toArray) P.settings.lidb cf := by
  unfold attB at hB
  have h0 := onOk_ok hB e
  have h1 := List.all_eq_true.mp h0 g hg
  have h2 := onOk_ok h1 hcf
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨a, b⟩, c⟩ := h2
  exact ⟨⟨a, b⟩, hid_eq (by rw [a, b]; exact expTable_W) refL_le c⟩

/-- **THE CERTIFICATE's LAW: where attB accepts, the attention's configuration is its twin**: no
  sort, no test on a
table of 65,536 rows, the table of exponentials the library's list: at all hashes o, scans P,
  layouts y, scales s. -/
theorem config_of_check (o : Nat → ByteArray → ByteArray) (P : PolScan) (y : Layer.Lay)
    (s : Layer.Scales) (mq : Nat → Nat) (hB : attB (some refL.toArray) 4096 P y s = true) :
    configO o P y s mq = configS (some refL.toArray) o P y s mq :=
  config_eq _ o P y s mq fun _ e _ hg cf hcf => (att_at hB e hg cf hcf).2

end OnBytes.Road.K4.Trial.AttLaws

#print axioms OnBytes.Road.K4.Trial.AttLaws.shape_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.shapeHid_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.okF_ofNat
#print axioms OnBytes.Road.K4.Trial.AttLaws.ask_tableOf
#print axioms OnBytes.Road.K4.Trial.AttLaws.rowKR_lt
#print axioms OnBytes.Road.K4.Trial.AttLaws.rowWH_lt
#print axioms OnBytes.Road.K4.Trial.AttLaws.rowKFD_lt
#print axioms OnBytes.Road.K4.Trial.AttLaws.layCall_ask
#print axioms OnBytes.Road.K4.Trial.AttLaws.asks_of_shape
#print axioms OnBytes.Road.K4.Trial.AttLaws.hid_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.plan_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.group_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.config_eq
#print axioms OnBytes.Road.K4.Trial.AttLaws.expTable_W
#print axioms OnBytes.Road.K4.Trial.AttLaws.refL_small
#print axioms OnBytes.Road.K4.Trial.AttLaws.refL_le
#print axioms OnBytes.Road.K4.Trial.AttLaws.att_at
#print axioms OnBytes.Road.K4.Trial.AttLaws.config_of_check
