-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/AllZeroAtPlans.lean: IN THE PLANNED LEDGER OF EVERY SEGMENT EVERY VIRTUAL ROW OF EVERY
ARRAY BEGINS AT COLUMN 0 (the field L0 of HRow, OnBytes/Model/Hide.lean). A definition and lemmas;
none of the library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `AllZero F`   every virtual row of every array of the ledger F begins at column 0 (`l0At`,
      Johnson/P1K8R/ZzRowsAtPlans.lean)
  `empty_l0`, `allZero_empty`, `allZero_push`   the empty array; the empty ledger; a ledger with one
      array more, whose rows begin at column 0
  `t2AddN_zero`, `t2AddP_zero`   the two routines that add an array (OnBytes/Model/Trees.lean) keep
      it
  **`addTreesF_allZero`**   addTreesF (OnBytes/Model/Tail.lean) keeps it
  `allZero_trimL`   freeing the weights keeps it
  `planG_all`, `planA_all`, `planH2_all`   at what each of the three planners returns
  `public_G_all`, `public_A_all`, `public_H_all`, **`public_allZero`**   at every plan in what
      Verify.publicOf returns
  **`built_allZero`**   in the goals' scope, under an opening of the description: at each of the 25
      built segments
By: Fo.ext_push, getD_push_last (OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean) · getD_out
(OnBytes/Tie/Pv/Tail/EndPort.lean) · forInX, jpX, bindX, seamPlan_cut and the cuts of planG_zMine,
planH2_zMine, public_A_zMine (FoZMade.lean, FoZRec.lean, FoZPublic.lean) · the walk of addTreesF's
first loop as in addTreesF_u3Tree (Johnson/Road/K4/Rec/U3Tree.lean) · `replicate_l0`, `l0At_trimL` ·
IM.ground_tails (Johnson/IMR/K8Seat.lean).
Limits. THE PLANNED LEDGER ALONE: nothing on the ledger of any state. The full size's 25 segments in
`built_allZero`.

-/
import Johnson.P1K8R.ZzRowsAtPlans
import OnBytes.Tie.Pv.Tail.EndPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Fo (pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan

/-- Every virtual row of every array begins at column 0. -/
def AllZero (F : Fork) : Prop := ∀ t e, l0At F t e = 0

/-- The empty array has no row. -/
theorem empty_l0 (e : Nat) : ((({} : HTree).rows).getD e {}).L0 = 0 := replicate_l0 0 e

theorem allZero_empty : AllZero {} := fun t e => by
  unfold l0At
  rw [OnBytes.Tie.Pv.Tail.getD_out ({} : Fork).trees t {} (Nat.not_lt_zero t)]
  exact empty_l0 e

/-- One array more. -/
theorem allZero_push {F : Fork} {X : HTree} (hF : AllZero F)
    (hX : ∀ e, (X.rows.getD e {}).L0 = 0) : AllZero { F with trees := F.trees.push X } := by
  intro t e
  show (((F.trees.push X).getD t {}).rows.getD e {}).L0 = 0
  rcases Nat.lt_trichotomy t F.trees.size with h | h | h
  · have k : (F.trees.push X).getD t {} = F.trees.getD t {} := (_root_.Fo.ext_push F X).2 t h
    rw [k]
    exact hF t e
  · subst h
    rw [_root_.Fo.getD_push_last]
    exact hX e
  · rw [OnBytes.Tie.Pv.Tail.getD_out (F.trees.push X) t {} (by rw [Array.size_push]; omega)]
    exact empty_l0 e

theorem t2AddN_zero {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2} (hF : AllZero F)
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) : AllZero F' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e2
    exact allZero_push hF fun e => replicate_l0 nv e

theorem t2AddP_zero {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2} (hF : AllZero F)
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) : AllZero F' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨e2, _⟩ := Prod.mk.inj e2
      subst e2
      exact allZero_push hF fun e => replicate_l0 1 e

/-- **addTreesF keeps it.** -/
theorem addTreesF_allZero {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (hF : AllZero F)
    (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) : AllZero G := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := bindX h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := bindX h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := bindX h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  have e := Except.ok.inj h
  obtain ⟨_, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e2
  have K1 : AllZero F1 := forInX _ (fun s : MProd Fork Tail2 => AllZero s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
        obtain ⟨_, hs⟩ := jpX hs
        exact ⟨_, (Except.ok.inj hs).symm, t2AddN_zero hI hP⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    _ _ _ hF h1
  have K2 : AllZero F2 := forInX _ (fun s : MProd Fork Tail2 => AllZero s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, t2AddP_zero hI hP⟩)
    _ _ _ K1 h2
  have K3 : AllZero F3 := forInX _ (fun s : MProd Fork Tail2 => AllZero s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, t2AddP_zero hI hP⟩)
    _ _ _ K2 h3
  exact forInX _ (fun s : MProd Fork Tail2 => AllZero s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, t2AddP_zero hI hP⟩)
    _ _ _ (t2AddN_zero (t2AddN_zero K3 hZ) hB) h4

theorem allZero_trimL {F : Fork} (h : AllZero F) : AllZero F.trimL := fun t e => by
  rw [l0At_trimL]
  exact h t e

theorem planG_all (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : AllZero hp.Fp := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  have k : AllZero Fp := addTreesF_allZero allZero_empty hA
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact allZero_trimL k
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact allZero_trimL k
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_all (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : AllZero P.seam.Fp := by
  obtain ⟨seam0, -, h1, -⟩ := planA_rows0 settings i cf P e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact addTreesF_allZero allZero_empty hA

theorem planH2_all (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : AllZero hp.Fp := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact addTreesF_allZero allZero_empty hA
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_all (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : AllZero hp.Fp :=
  planG_all X.layers g _ hp (public_G h g hp hg)

theorem public_H_all (h : Verify.publicOf pol KL layout = .ok X) : AllZero X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact allZero_trimL (planH2_all _ _ _ _ _ _ _ H0 h0)

theorem public_A_all (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : AllZero a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show AllZero a0.seam.Fp
    exact planA_all _ _ _ a0 m2
  · simp at e1

/-- **At every plan in what publicOf returns.** -/
theorem public_allZero (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → AllZero hp.Fp) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → AllZero a.seam.Fp) ∧
      AllZero X.H.Fp :=
  ⟨public_G_all h, public_A_all h, public_H_all h⟩

end

/-- **At each of the 25 built segments.** -/
theorem built_allZero {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : AllZero Xl.Fp := by
  obtain ⟨hT, X24, e24, -, f24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases hh : l = 24
  · subst hh
    obtain rfl : X24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [f24]
    exact (public_allZero O.public).2.2
  · obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    · obtain ⟨hp, -, X', -, ehp, -, e3', -, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [hfp]
      exact (public_allZero O.public).1 g hp ehp
    · obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', -, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [hfp]
      exact (public_allZero O.public).2.1 g q eq

end P1K8

#print axioms P1K8.empty_l0
#print axioms P1K8.allZero_empty
#print axioms P1K8.allZero_push
#print axioms P1K8.t2AddN_zero
#print axioms P1K8.t2AddP_zero
#print axioms P1K8.addTreesF_allZero
#print axioms P1K8.allZero_trimL
#print axioms P1K8.planG_all
#print axioms P1K8.planA_all
#print axioms P1K8.planH2_all
#print axioms P1K8.public_G_all
#print axioms P1K8.public_A_all
#print axioms P1K8.public_H_all
#print axioms P1K8.public_allZero
#print axioms P1K8.built_allZero
