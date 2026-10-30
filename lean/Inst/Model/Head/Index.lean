-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/Index.lean: index sets, lookup families and matrix layout of the head segment.

Numbers and maps on numbers only, at the reference parameters (`ppref`): no field, no cell.
  `Req`          what the head reads of a request (Inst/Model/ProgramR.lean): r, e, the checked
                 token of each position, the policy's three numbers; `Req.rho`: ρ_i = [r ≤ i < e]
  `Fam`, `call`  the nine families of looked-up values and the six calls of the lookup argument. By
                 `key` in Policy/Rel/LedgerHead.lean the families are: NF, NFH (the rounding of the
                 normalisation), CNF (its clamp), HD0, HD1, HD2 (top, middle and low digit of a
                 margin), HE0, HE1 (the table EX at the middle digit), ROW (the ledger bytes)
  `pos`          in every call (s, x) ↦ pos_s[x] is a bijection onto the columns in use (`pos_inj`,
                 `pos_lt`, `pos_surj`); runs of 64 stay together if s ≠ ROW (`pos_run`)
  `Mx`, `colOf`, `rowOf`, `placeB`, `padPos`
                 the matrices; where they hold the features and the array B; the padding positions
A ledger byte is one of the 120 auxiliary bytes of a position (`Dv`, Inst/Model/Head/Trace.lean).
The matrix x is borrowed from the last feed-forward segment. B is the array of the lookup argument's
multiplicity bits. A tree is a group of 2^27 looked-up values; calls 1 to 3 have two trees each,
calls 4 to 6 one (`size`).
Notation:
  θ: in the doc comment of `Req` the policy's number (`AcceptancePolicy.theta`, Inst/Model/ProgramR.lean); at
    `padPos` and `placeB` the number of a tree.
  ϕ_θ: the number of padding positions of tree θ (`padPos c`: that of the last tree of call c).
  J_c: `cols c`; ȷ: the number of a column of a call.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.ProgramR
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model.Head

/-! ## Indices -/

/-- i < 1,024 is a position, j < 5,120 a channel, ι < 202,048 a vocabulary entry, n < 120 the
number of a ledger byte -/
def nT : ℕ := 1024
def nD : ℕ := 5120
def nV : ℕ := 202048
def nB : ℕ := 120
theorem nums_ppref : nT = ppref.T ∧ nD = ppref.d ∧ nV = ppref.V := ⟨rfl, rfl, rfl⟩

/-- What the head reads of a request and of the policy: the two numbers that bound the covered
positions; for each position the token that is checked there (the next token of the request; at the
last position the announced token); the three numbers of the acceptance policy. The type includes
none of the verifier's public checks (r < e ≤ T; y = 0 if e < T; every token below V; θ ≤ C, cap ≤
T, cap < 2^16): each theorem assumes what it needs (`Req.OK`; `Head3` of Inst/Model/ProgramR.lean
and `AcceptancePolicy.OK` of Inst/Model/ProgramRPol.lean; `Fit` of Inst/Model/Head/PolicyDefs.lean). -/
structure Req where
  r : ℕ
  e : ℕ
  win : ℕ → ℕ
  pol : AcceptancePolicy

instance : Inhabited Req := ⟨⟨0, 0, fun _ => 0, ⟨0, 0, 0⟩⟩⟩

/-- ρ_i = [r ≤ i < e]: the indicator of the covered positions -/
def Req.rho (q : Req) (i : ℕ) : ℤ := if q.r ≤ i ∧ i < q.e then 1 else 0
/-- ρC_i = [r ≤ i < min(e, T − 1)], T − 1 = 1,023: the indicator of the counted positions: covered,
and the checked token is a token of the request -/
def Req.rhoC (q : Req) (i : ℕ) : ℤ := if q.r ≤ i ∧ i < min q.e 1023 then 1 else 0
/-- NB = min(e, T − 1) − r: the number of counted positions -/
def Req.NB (q : Req) : ℕ := min q.e 1023 - q.r
/-- The request for the next token after 1,024 tokens, with the announced token y: r = 1,023, e =
1,024; y is put at every position and read only at 1,023. It has no counted position, so nothing
reads the policy's numbers. (The whole model passes `Req.of pol (Instance.nextOf prompt y)`, another
term; there too the four claims on the hidden numbers hold of themselves: `hidden_last`,
Inst/Model/RequestGuards.lean.) -/
def Req.last (y : ℕ) : Req := ⟨1023, 1024, fun _ => y, ⟨0, 0, 0⟩⟩
/-- what the head reads of an instance, under the policy pol: r, e, at position t the token x_(t+1),
with x_T := y (`Instance.w`, Inst/Model/ProgramR.lean), and the policy's three numbers -/
def Req.of (pol : AcceptancePolicy) (x : Instance ppref) : Req := ⟨x.r, x.e, x.w, pol⟩
/-- every checked token is below V -/
def Req.OK (q : Req) : Prop := ∀ i, q.win i < nV
theorem Req.of_ok (pol : AcceptancePolicy) (x : Instance ppref) : (Req.of pol x).OK := fun i => x.w_lt i
theorem Req.rhoC_01 (q : Req) (i : ℕ) : q.rhoC i = 0 ∨ q.rhoC i = 1 := by
  unfold Req.rhoC
  split
  · exact Or.inr rfl
  · exact Or.inl rfl
/-- a counted position is covered -/
theorem Req.rho_of_rhoC (q : Req) {i : ℕ} (h : q.rhoC i = 1) : q.rho i = 1 := by
  unfold Req.rhoC at h
  unfold Req.rho
  split at h
  · rename_i hc
    rw [if_pos ⟨hc.1, by omega⟩]
  · exact absurd h (by norm_num)
/-- no counted position: NB = 0 -/
theorem Req.NB_of_rhoC (q : Req) (h : ∀ i, q.rhoC i = 0) : q.NB = 0 := by
  by_contra hne
  have h1 := h q.r
  unfold Req.NB at hne
  unfold Req.rhoC at h1
  rw [if_pos ⟨le_refl _, by omega⟩] at h1
  exact absurd h1 (by norm_num)
theorem Req.rhoC_last (y i : ℕ) : (Req.last y).rhoC i = 0 := by
  unfold Req.rhoC Req.last
  rw [if_neg (by simp only; omega)]
theorem Req.NB_last (y : ℕ) : (Req.last y).NB = 0 := by
  unfold Req.NB Req.last
  simp only
  omega
/-- the counted positions of an instance -/
theorem Req.rhoC_of (pol : AcceptancePolicy) (x : Instance ppref) (i : ℕ) :
    (Req.of pol x).rhoC i = if i ∈ x.cnt then 1 else 0 := by
  unfold Req.rhoC Req.of Instance.cnt
  simp only [Finset.mem_Ico]
  rfl
theorem Req.NB_of (pol : AcceptancePolicy) (x : Instance ppref) : (Req.of pol x).NB = x.NB := rfl

/-- An instance that the head reads as q, defined for every q: token t is q.win (t − 1), the
announced token is q.win 1,023, and r, e are q's. All four are clamped into their ranges (a token to
at most V − 1, r and e to at most T), so they have these values only where q's own numbers are in
range (`Req.OK`; `Req.inst_w`, `Req.inst_of`). The honest prover's rule for the hidden numbers
(Inst/Model/Head/PolicyHonest.lean) is written for instances, while the head's honest state is built
from a `Req` only; this function turns a `Req` into an instance. Token 0, which no position checks,
is q.win 0.
-/
def Req.inst (q : Req) : Instance ppref where
  prompt := fun t => ⟨min (q.win (t.val - 1)) 202047, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  y := ⟨min (q.win 1023) 202047, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  rF := ⟨min q.r 1024, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  eF := ⟨min q.e 1024, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem Req.inst_r (q : Req) : q.inst.r = min q.r 1024 := rfl
theorem Req.inst_e (q : Req) : q.inst.e = min q.e 1024 := rfl
/-- if `q.OK` holds, `q.inst` has q's checked token at each of the 1,024 positions -/
theorem Req.inst_w (q : Req) (hq : q.OK) {i : ℕ} (hi : i < nT) : q.inst.w i = q.win i := by
  have h1 := hq i
  have h2 := hq 1023
  unfold nV at h1 h2
  unfold nT at hi
  unfold Instance.w Instance.tok
  by_cases h : i + 1 < ppref.T
  · rw [dif_pos h]
    show min (q.win (i + 1 - 1)) 202047 = q.win i
    rw [Nat.add_sub_cancel]
    omega
  · rw [dif_neg h]
    have e : i = 1023 := by
      have : ¬ i + 1 < 1024 := h
      omega
    show min (q.win 1023) 202047 = q.win i
    rw [e]
    omega
theorem Req.mem_inst_cnt (q : Req) {i : ℕ} : i ∈ q.inst.cnt ↔ q.r ≤ i ∧ i < min q.e 1023 := by
  unfold Instance.cnt
  rw [Finset.mem_Ico, q.inst_r, q.inst_e]
  show min q.r 1024 ≤ i ∧ i < min (min q.e 1024) (1024 - 1) ↔ _
  omega
theorem Req.inst_NB (q : Req) : q.inst.NB = q.NB := by
  unfold Instance.NB Req.NB
  rw [q.inst_r, q.inst_e]
  show min (min q.e 1024) (1024 - 1) - min q.r 1024 = _
  omega
theorem Req.rhoC_inst (q : Req) (i : ℕ) : q.rhoC i = if i ∈ q.inst.cnt then 1 else 0 := by
  unfold Req.rhoC
  simp only [q.mem_inst_cnt]
theorem Req.rho_inst (q : Req) {i : ℕ} (hi : i < nT) :
    q.rho i = if q.inst.r ≤ i ∧ i < q.inst.e then 1 else 0 := by
  unfold Req.rho
  unfold nT at hi
  rw [q.inst_r, q.inst_e]
  by_cases h : q.r ≤ i ∧ i < q.e
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
/-- `(Req.of pol x).inst` has the r, the e, the checked tokens and the announced token of x -/
theorem Req.inst_of (pol : AcceptancePolicy) (x : Instance ppref) :
    (Req.of pol x).inst.r = x.r ∧
    (Req.of pol x).inst.e = x.e ∧
    (Req.of pol x).inst.w = x.w ∧
    (Req.of pol x).inst.y.val = x.y.val := by
  have hr : x.r ≤ 1024 := Nat.lt_succ_iff.1 x.rF.isLt
  have he : x.e ≤ 1024 := x.e_le
  have hy : x.w 1023 = x.y.val := by
    unfold Instance.w Instance.tok
    rw [dif_neg (by show ¬ 1023 + 1 < 1024; omega)]
  have hyl : x.y.val < 202048 := x.y.isLt
  refine ⟨?_, ?_, funext fun i => ?_, ?_⟩
  · show min x.r 1024 = x.r
    omega
  · show min x.e 1024 = x.e
    omega
  · by_cases hi : i < nT
    · exact (Req.of pol x).inst_w (Req.of_ok pol x) hi
    · unfold nT at hi
      unfold Instance.w Instance.tok
      rw [dif_neg (by show ¬ i + 1 < 1024; omega), dif_neg (by show ¬ i + 1 < 1024; omega)]
      show min (x.w 1023) 202047 = x.y.val
      omega
  · show min (x.w 1023) 202047 = x.y.val
    omega
theorem Req.rho_last (y i : ℕ) (hi : i < nT) : (Req.last y).rho i = if i = 1023 then 1 else 0 := by
  unfold Req.rho Req.last nT at *
  by_cases h : i = 1023
  · subst h; simp
  · rw [if_neg h, if_neg (by simp only; omega)]
theorem Req.rho_01 (q : Req) (i : ℕ) : q.rho i = 0 ∨ q.rho i = 1 := by
  unfold Req.rho
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Families and calls -/

inductive Fam
  | NF | NFH | HD0 | HD1 | ROW | HD2 | HE0 | HE1 | CNF
  deriving DecidableEq, Repr, Fintype

/-- n_s: family s has the indices x < n_s -/
def len : Fam → ℕ
  | .NF => 5120 | .NFH => 5120 | .HD0 => 202048 | .HD1 => 202048 | .ROW => 120 | .HD2 => 202048
  | .HE0 => 131072 | .HE1 => 70976 | .CNF => 5120

/-- the call of a family, 1 to 6 -/
def call : Fam → ℕ
  | .NF => 1 | .NFH => 1 | .HD0 => 1 | .HD1 => 2 | .ROW => 3 | .HD2 => 3
  | .HE0 => 4 | .HE1 => 5 | .CNF => 6

/-- a_c: call c has 2^{a_c} looked-up values, in J_c = 2^{a_c − 10} columns -/
def size (c : ℕ) : ℕ := if c ≤ 3 then 28 else 27
def cols (c : ℕ) : ℕ := 2 ^ (size c - 10)

/-- x_s = 131,072 for s = HE1 and x_s = 0 for every other family: index x of the family is
the index x_s + x of its arrays -/
def shift : Fam → ℕ
  | .HE1 => 131072
  | _ => 0

/-- pos_s[x], the column of index x of family s:
call 1: HD0 [0, 131072) → 0; HD0 [131072, 196608) → 131072; NF [0, 4096) → 196608; NFH [0, 4096) →
200704; HD0 [196608, 200704) → 204800; NF [4096, 5120) → 208896;
NFH [4096, 5120) → 209920; HD0 [200704, 201728) → 210944; HD0 [201728, 201984) → 211968; HD0
[201984, 202048) → 212224;
call 3: HD2 [0, 201984) → 0; ROW [0, 64) → 201984; HD2 [201984, 202048) → 202048; ROW [64, 96) →
202112; ROW [96, 112) → 202144; ROW [112, 120) → 202160;
calls 2, 4, 5, 6: x → x. -/
def pos : Fam → ℕ → ℕ
  | .HD0, x => if x < 196608 then x else if x < 200704 then 204800 + (x - 196608) else 210944 + (x - 200704)
  | .NF, x => if x < 4096 then 196608 + x else 208896 + (x - 4096)
  | .NFH, x => if x < 4096 then 200704 + x else 209920 + (x - 4096)
  | .HD2, x => if x < 201984 then x else 202048 + (x - 201984)
  | .ROW, x => if x < 64 then 201984 + x else 202112 + (x - 64)
  | _, x => x

/-- first column that no family takes (in call 4: all columns are taken) -/
def used : ℕ → ℕ
  | 1 => 212288 | 2 => 202048 | 3 => 202168 | 4 => 131072 | 5 => 70976 | 6 => 5120 | _ => 0

/-- In every call the map (s, x) ↦ pos_s[x], x < n_s, is injective. -/
theorem pos_inj {s s' : Fam} {x x' : ℕ} (hc : call s = call s') (hx : x < len s)
    (hx' : x' < len s') (h : pos s x = pos s' x') : s = s' ∧ x = x' := by
  cases s <;> cases s' <;> simp only [call] at hc <;> first | omega | skip
  all_goals
    simp only [pos, len] at h hx hx'
    first
      | (refine ⟨rfl, ?_⟩; (try split_ifs at h) <;> omega)
      | (exfalso; (try split_ifs at h) <;> omega)

/-- Its values are below `used` of the call; by `pos_surj` they are all these columns. -/
theorem pos_lt (s : Fam) {x : ℕ} (hx : x < len s) : pos s x < used (call s) := by
  cases s <;> simp only [pos, len, used, call] at hx ⊢ <;> (try split_ifs) <;> omega

theorem pos_surj {c col : ℕ} (h : col < used c) :
    ∃ s x, call s = c ∧ x < len s ∧ pos s x = col := by
  match c, h with
  | 1, h =>
    simp only [used] at h
    by_cases h1 : col < 196608
    · exact ⟨.HD0, col, rfl, by simp only [len]; omega, by simp only [pos, if_pos h1]⟩
    by_cases h2 : col < 200704
    · exact ⟨.NF, col - 196608, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    by_cases h3 : col < 204800
    · exact ⟨.NFH, col - 200704, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    by_cases h4 : col < 208896
    · exact ⟨.HD0, col - 8192, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    by_cases h5 : col < 209920
    · exact ⟨.NF, col - 204800, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    by_cases h6 : col < 210944
    · exact ⟨.NFH, col - 205824, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    · exact ⟨.HD0, col - 10240, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
  | 2, h => exact ⟨.HD1, col, rfl, h, rfl⟩
  | 3, h =>
    simp only [used] at h
    by_cases h1 : col < 201984
    · exact ⟨.HD2, col, rfl, by simp only [len]; omega, by simp only [pos, if_pos h1]⟩
    by_cases h2 : col < 202048
    · exact ⟨.ROW, col - 201984, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    by_cases h3 : col < 202112
    · exact ⟨.HD2, col - 64, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
    · exact ⟨.ROW, col - 202048, rfl, by simp only [len]; omega,
        by simp only [pos]; split_ifs <;> omega⟩
  | 4, h => exact ⟨.HE0, col, rfl, h, rfl⟩
  | 5, h => exact ⟨.HE1, col, rfl, h, rfl⟩
  | 6, h => exact ⟨.CNF, col, rfl, h, rfl⟩
  | 0, h => simp [used] at h
  | n + 7, h => simp [used] at h

/-- Let s ≠ ROW. For all x' < n_s / 64 and x'' < 64: pos_s[64 x' + x''] = pos_s[64 x'] + x'', and 64
divides pos_s[64 x'] -/
theorem pos_run {s : Fam} (hs : s ≠ .ROW) {x' x'' : ℕ} (h' : x' < len s / 64) (h'' : x'' < 64) :
    pos s (64 * x' + x'') = pos s (64 * x') + x'' ∧ 64 ∣ pos s (64 * x') := by
  cases s <;> first | exact absurd rfl hs | skip
  all_goals
    first
      | exact ⟨rfl, Dvd.intro _ rfl⟩
      | (simp only [pos, len] at h' ⊢
         constructor
         · split_ifs <;> omega
         · split_ifs <;> omega)

/-- The columns fit: used c ≤ J_c (`used_le`, below; J_c is `cols c`).
The padding positions of the nine trees: ϕ_θ = 0; 51,052,544; 0; 61,538,304; 0; 61,415,424; 0;
61,538,304; 128,974,848.
Tree b of a call with two trees holds the columns with ⌊ȷ / 2^17⌋ = b, and all columns that no
family takes are in the second tree. -/
def padPos (c : ℕ) : ℕ := 1024 * (cols c - used c)
theorem used_le : ∀ c, used c ≤ cols c := by
  intro c
  match c with
  | 0 => simp [used]
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | n + 7 => simp [used]
theorem padPos_values :
    padPos 1 = 51052544 ∧ padPos 2 = 61538304 ∧ padPos 3 = 61415424 ∧ padPos 4 = 0 ∧
    padPos 5 = 61538304 ∧ padPos 6 = 128974848 := by
  decide
theorem second_tree : 2 ^ 17 ≤ used 1 ∧ 2 ^ 17 ≤ used 2 ∧ 2 ^ 17 ≤ used 3 := by decide

/-! ## Matrices and features -/

/-- the matrices: hf (its four parts taken together), hd, hr, b, and the borrowed x -/
inductive Mx
  | hf | hd | hr | b | x
  deriving DecidableEq, Repr

/-- n_1 (rows) and n_2 (columns); hf: 4 · 4,816 columns -/
def n1 : Mx → ℕ
  | .hf => 2 ^ 16 | .hd => 2 ^ 14 | .hr => 2 ^ 13 | .b => 2 ^ 15 | .x => 2 ^ 16
def n2 : Mx → ℕ
  | .hf => 19264 | .hd => 640 | .hr => 15 | .b => 576 | .x => 400
/-- A matrix with n_1 rows holds n_1 / 2^10 consecutive features in a column -/
def perCol (m : Mx) : ℕ := n1 m / 2 ^ 10
/-- feature φ at position i is the cell in column ⌊φ / (n_1 / 2^10)⌋ and row (φ mod (n_1 / 2^10))
2^10 + i -/
def colOf (m : Mx) (φ : ℕ) : ℕ := φ / perCol m
def rowOf (m : Mx) (φ i : ℕ) : ℕ := (φ % perCol m) * 2 ^ 10 + i

/-- the features of the arrays: the feature that holds cell l of the value with the index j, ι or
n -/
def fX (l j : ℕ) : ℕ := 5120 * l + j
def fNw (l j : ℕ) : ℕ := 5120 * l + j
def fRn (l j : ℕ) : ℕ := 10240 + 5120 * l + j
def fD1 (l v : ℕ) : ℕ := 20480 + 202048 * l + v
def fD2 (v : ℕ) : ℕ := 424576 + v
def fEx (l v : ℕ) : ℕ := 626624 + 202048 * l + v
def fNrm (l j : ℕ) : ℕ := 5120 * l + j
/-- the numbers of features that hold cells of the trace; hf has 128 filler features after them -/
def nFeat : Mx → ℕ
  | .hf => 1232768 | .hd => 10240 | .hr => 120 | .b => 0 | .x => 25600

/-- The 1,232,768 = 4 · 5,120 + 6 · 202,048 features of hf are followed by 128 filler features,
which fill the last part; hd, hr and x are full -/
theorem features_fill :
    nFeat .hf = 4 * 5120 + 6 * 202048 ∧
    nFeat .hf + 128 = perCol .hf * n2 .hf ∧
    nFeat .hd = perCol .hd * n2 .hd ∧
    nFeat .hr = perCol .hr * n2 .hr ∧
    nFeat .x = perCol .x * n2 .x ∧
    fEx 2 202047 + 1 = nFeat .hf := by decide

/-- The bit B[u, θ, π] is in column 64 θ + ⌊u / 2^10⌋ and row 32 (u mod 2^10) + π -/
def placeB (u θ π : ℕ) : ℕ × ℕ := (32 * (u % 2 ^ 10) + π, 64 * θ + u / 2 ^ 10)
theorem placeB_lt {u θ π : ℕ} (hu : u < 2 ^ 16) (hθ : θ < 9) (hπ : π < 32) :
    (placeB u θ π).1 < n1 .b ∧ (placeB u θ π).2 < n2 .b := by
  simp only [placeB, n1, n2]
  omega

/-- The matrices of `Mx`. Together they have m_Z = 385,024 rows (the four parts of hf counted one by
one) -/
theorem mZ : 4 * n1 .hf + n1 .hd + n1 .hr + n1 .b + n1 .x = 385024 := by decide

/-! ## The rule that `pos` follows, by evaluation at both ends of each piece
Cut each family into pieces by the binary expansion of n_s; sort the pieces of a call by size,
largest first, keeping the order of pieces of equal size; give them consecutive columns, starting at
column 0. -/

/-- the pieces (family, first index, size) of a family, largest first -/
def piecesOf (s : Fam) : List (Fam × ℕ × ℕ) :=
  ((List.range 18).reverse.foldl
    (fun (acc : List (Fam × ℕ × ℕ) × ℕ) b =>
      if (len s / 2 ^ b) % 2 = 1 then (acc.1 ++ [(s, acc.2, 2 ^ b)], acc.2 + 2 ^ b) else acc)
    ([], 0)).1
/-- the pieces of a call, sorted by size (stable), each with its first column -/
def placed (fams : List Fam) : List (Fam × ℕ × ℕ × ℕ) :=
  (((fams.flatMap piecesOf).mergeSort fun a b => b.2.2 ≤ a.2.2).foldl
    (fun (acc : List (Fam × ℕ × ℕ × ℕ) × ℕ) p =>
      (acc.1 ++ [(p.1, p.2.1, p.2.2, acc.2)], acc.2 + p.2.2)) ([], 0)).1
#guard (placed [.NF, .NFH, .HD0]).all fun p => pos p.1 p.2.1 == p.2.2.2 && pos p.1 (p.2.1 + p.2.2.1 - 1) == p.2.2.2 + p.2.2.1 - 1
#guard (placed [.ROW, .HD2]).all fun p => pos p.1 p.2.1 == p.2.2.2 && pos p.1 (p.2.1 + p.2.2.1 - 1) == p.2.2.2 + p.2.2.1 - 1
#guard (placed [.NF, .NFH, .HD0]).length == 10 && (placed [.ROW, .HD2]).length == 10

end Inst.Model.Head
