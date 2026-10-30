-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SecondAtPlain.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT: `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES OF THE BATCHING BLOCK, FROM PREMISES ON
THE STATE IN FRONT AND SENTENCES ON THE SEGMENT's OTHER RUNS OF CLAIMS, EACH AT THE STATE AT WHICH
THE RUN IS CALLED. A definition and lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding. An assembly.

  `drawn_frame`   behind the batching's draw the ledger has the frame (Fo.Frame,
      OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean) of the ledger in front
  `walk_trees`   the runs of a plain segment leave the ledger's arrays. ITS STEPS ARE THOSE IN THE
      MIDDLE OF `open_at_link` (Johnson/Desc/K8/Honest/OpenAtLink.lean), whose statement does not
      say it. `Gathers` (FallCount.lean) has the like by frame, under an "exists"
  `Added8.coefOK`   what the declared weights' laws ask (Fo.CoefOK), carried from the data and a
      ledger in front to the data and the ledger behind the adding
  `ApartOne tl cl`   the claim names neither the digits' array nor a matrix's array of symbols: the
      body of `OthersApart` (SecondOpen.lean) at one claim
  **`secondEqs_at_plain`**   the sentence of the title. Its end is the premise of `second_at_link`
      (SecondFew.lean) that speaks of `SecondEqs`. The invariants are letters
  `second_at_plain`   `second_at_link` under it: the count at a plain segment, without the premise
      that `SecondEqs` holds behind the batching. One premise still names `SecondEqs`: the one that
      says what a "no" means. The bound n is a letter
By: `open_at_link` · `Added8.secondEqs` (SecondOpen.lean) · `others_of_walk`
(Johnson/Desc/K8/Honest/OthersAtLink.lean) · `pre_one`, `post_one` (GathersPlain.lean) ·
`drawnAt_ok`, `drawn_trees` (FallDraw.lean) · Fo.frame_fill, Fo.frame_same, Fo.frame_trees
(OnBytes/Tie/Pv/Lookup/Ends/FoFramePass.lean) · LinkJoin.coefOK_frame
(Johnson/Desc/First/Link/Law/FullFour.lean) · LinkJoin.coefOK_congr (OkJoin.lean) · eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean).
Limits. EVERY PREMISE IS SHOWN OF NO STATE HERE. Which invariants serve all runs of a segment is not
said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.SecondOpen
import Johnson.Desc.K8.Honest.OpenAtLink
import Johnson.Desc.K8.Honest.OthersAtLink
import Johnson.Desc.First.Link.Law.FullFour
import OnBytes.Tie.Pv.Lookup.Ends.FoFramePass

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **Behind the batching's draw the ledger has the frame of the ledger in front.** -/
theorem drawn_frame (p : K9.Where) (s t : S) (d : Fmt.Drawn) (hdr : drawnAt p s d = .ok t)
    (F : Fork) (hF : s.fork? = some F) : ∃ x, K9.atS.get? t = some x ∧ Fo.Frame F x.F := by
  obtain ⟨a0, x0, o, ha0, -, hdc, htt⟩ := drawnAt_ok p s t d hdr
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have hFa : a0.F = F := Option.some.inj ((K9.get_fork s a0 ha0).symm.trans hF)
  refine ⟨a', by rw [htt]; exact ha', ?_⟩
  rw [hF']
  refine (Fo.frame_fill F a0.L.list).trans (Fo.frame_same ?_)
  rw [drawn_trees _ _ _ _ _ _ _ hdc, hFa]

/-- **The runs of a plain segment leave the ledger's arrays.** -/
theorem walk_trees {L : Link S Claim} {pre post : List (Nat × String)} (Hpre : PreOk L pre)
    (Hpost : PostOk L post) {t e : S} {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ : Fork}
    {tl tl' : HTailF2} {funs : Array HFun}
    (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs) (x : K9.Part)
    (hx : K9.atS.get? t = some x) (Y : Fork) (hY : e.fork? = some Y) : Y.trees = x.F.trees := by
  obtain ⟨c, -, -, -, -, c5⟩ := pre_one L pre Hpre _ _ W.a1
  obtain ⟨x₁, hx₁, s₁⟩ := c5 x hx
  obtain rfl : x₁.F = F₁ := Option.some.inj ((K9.get_fork _ _ hx₁).symm.trans W.a2)
  obtain ⟨x₂, hx₂, hF₂, -, -, -, -, -⟩ := K9L.get_put e₁ x₁ hx₁ tl' F₂
  obtain ⟨b, -, -, -, b5⟩ := post_one L post Hpost _ _ W.a7
  rw [W.a6] at b5
  obtain ⟨y, hy, s₃⟩ := b5 x₂ hx₂
  obtain rfl : y.F = Y := Option.some.inj ((K9.get_fork _ _ hy).symm.trans hY)
  have s₂ : SameSums x₁.F x₂.F := by
    rw [hF₂]
    exact SameSums.ofSide (eq_side W.a5)
  exact ((s₁.trans s₂).trans s₃).trees

/-- What the declared weights' laws ask, carried from the data and a ledger in front to the data and
the ledger behind the adding. -/
theorem Added8.coefOK {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ F : Fork}
    {fr k8 bk : List Claim} {n₀ : Nat} (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀)
    (hfr : Fo.Frame F G) (T : Fo.CoefOK tl F) : Fo.CoefOK tl' G :=
  LinkJoin.coefOK_congr
    (eq_same (fun t : HTailF2 => LinkJoin.g9 t) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl))
    (LinkJoin.coefOK_frame hfr T)

/-- A claim names neither the digits' array nor a matrix's array of symbols. -/
def ApartOne (tl : HTailF2) (cl : Claim) : Prop :=
  NamesNot tl.ix.ZZ cl ∧ ∀ mu, mu < tl.NM → NamesNot (tl.gtTree.getD mu 0) cl

/-- **AT A PLAIN SEGMENT: `SecondEqs` BEHIND EVERY YES OF THE BATCHING BLOCK, FROM PREMISES IN FRONT
AND SENTENCES ON THE OTHER RUNS, EACH AT THE STATE AT WHICH IT IS CALLED.** The end is the premise
of `second_at_link` (Johnson/Desc/K8/Honest/SecondFew.lean). -/
theorem secondEqs_at_plain (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (hS : SecondFront tl F) (T : Fo.CoefOK tl F)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R)
    (Inv Inv₂ : S → Prop)
    (hpre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, ApartOne tl cl) ∧ Inv u')
    (hk8 : ∀ (u : S) (tl₀ tl₁ : HTailF2) (F₀ F₂ : Fork) (funs₀ : Array HFun) (k8 : List Claim)
      (n : Nat), Inv u → u.fork? = some F₀ → u.tl? = some tl₀ → u.funs? = some funs₀ →
      equations n tl₀ funs₀ F₀ = .ok (tl₁, F₂, k8) → Inv₂ ((u.putTl tl₁).putFork F₂))
    (hpost : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, ApartOne tl cl) ∧ Inv₂ u')
    (hInv : ∀ (x : Cb.Gl.E) (t : S), drawnAt p s (chiAt x) = .ok t → Inv t) :
    ∀ (x : Cb.Gl.E) (t' : S) (tl' : HTailF2) (G : Fork), batch s [⟨[], chiAt x⟩] = .ok t' →
      tlForkP.get? t' = some (tl', G) → SecondEqs tl' G := by
  intro x t' tl' G hbt hget
  obtain ⟨t, e, e₁, e₂, cls, fr, k8, bk, tl₁, Y, G₁, F₁, F₂, hdr, -, W, hY, hget₁, A, -, -, hsh⟩ :=
    open_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  obtain ⟨rfl, rfl⟩ : tl₁ = tl' ∧ G₁ = G := Prod.mk.inj (Option.some.inj (hget₁.symm.trans hget))
  obtain ⟨xx, hx, fx⟩ := drawn_frame p s t _ hdr F hF
  have fG : Fo.Frame F G₁ :=
    (fx.trans (Fo.frame_same (walk_trees Hpre Hpost W xx hx Y hY))).trans
      (Fo.frame_trees A.core.2.2.1)
  obtain ⟨o1, o2⟩ := others_of_walk W Inv Inv₂ (ApartOne tl) hpre hk8 hpost (hInv _ _ hdr)
  refine A.secondEqs hsh hS (fun cl hcl => hcl.elim (o1 cl) (o2 cl)) (A.coefOK fG T)
    fun nbW Wn hW w hw => ?_
  rw [(fG.2 _).1]
  exact hR nbW Wn hW w hw

/-- **THE COUNT OF THE SECOND FALL AT A PLAIN SEGMENT, WITHOUT THE PREMISE THAT `SecondEqs` HOLDS
BEHIND THE BATCHING**: `second_at_link` (Johnson/Desc/K8/Honest/SecondFew.lean) under
`secondEqs_at_plain`. (hno), which says what a "no" means, still names `SecondEqs`. -/
theorem second_at_plain (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (n : Nat) (no : S → Bool)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hno : ∀ t' tl' G, tlForkP.get? t' = some (tl', G) → no t' = true →
      ∃ g₀ jo nbW W, tl'.heard = some g₀ ∧ tl'.joinObj9 = some jo ∧
        tl'.wants = some (nbW, W) ∧ ¬ (SecondEqs tl' G ∧ SecondRest tl' G))
    (hOw : ∀ tl F, s.tl? = some tl → s.fork? = some F → SecondLaid tl F ∧
      (∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W) ∧
      secondN tl ≤ n)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (hS : SecondFront tl F) (T : Fo.CoefOK tl F)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R)
    (Inv Inv₂ : S → Prop)
    (hpre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, ApartOne tl cl) ∧ Inv u')
    (hk8 : ∀ (u : S) (tl₀ tl₁ : HTailF2) (F₀ F₂ : Fork) (funs₀ : Array HFun) (k8 : List Claim)
      (n : Nat), Inv u → u.fork? = some F₀ → u.tl? = some tl₀ → u.funs? = some funs₀ →
      equations n tl₀ funs₀ F₀ = .ok (tl₁, F₂, k8) → Inv₂ ((u.putTl tl₁).putFork F₂))
    (hpost : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, ApartOne tl cl) ∧ Inv₂ u')
    (hInv : ∀ (x : Cb.Gl.E) (t : S), drawnAt p s (chiAt x) = .ok t → Inv t) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ n :=
  second_at_link L ⟨i, pre, post, hord, Hpre, Hpost, tEq⟩ p batch s n no hb hno hOw
    (secondEqs_at_plain L i pre post hord Hpre Hpost tEq p batch s tl F funs hb ht hF hf hS T hR
      Inv Inv₂ hpre hk8 hpost hInv)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.drawn_frame
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_trees
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.coefOK
#print axioms VerifiableInference.Desc.First.K8.Honest.secondEqs_at_plain
#print axioms VerifiableInference.Desc.First.K8.Honest.second_at_plain
