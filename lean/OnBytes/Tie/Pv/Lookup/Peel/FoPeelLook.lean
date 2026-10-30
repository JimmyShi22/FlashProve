-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPeelLook.lean: the lookup of a sub-proof is taken off the front of a
file's
written rounds.

A block is taken off the front of written rounds as in OnBytes/Slice/Peel.lean: if the block's input
statement has no witness, the prover has lost in the block's rounds and the rounds behind them,
provided
it has lost in the rounds behind after every transcript of the block's rounds that has no image, and
after every one whose image leads to an output statement without a witness. Here the maps from the
written rounds are those of OnBytes/Flat/CarrySkip.lean (CarryS: a written round may have no typed
round), and the block is the typed lookup Cb.Fo.forB over the challenge field, whose knowledge
soundness is Cb.Fo.holeCgl.

What the file states.
 - peelS: the step of OnBytes/Slice/Peel.lean for CarryS: for any reduction with Know.
For every record of public numbers h that passes the test FoNums.ok, every layout L, every joint R0
of the
caller that rides along, every tuple m of committed messages, every written shape s with maps F to
the
lookup's typed rounds, error counts ε' of s that bear the lookup's (CarryS.Fits), and every shape t:
 - NoIn: the lookup's input statement has no witness at m: for no further witness both R0's relation
   holds
   and each call's keys, read off m, all lie in that call's table.
 - NoOut a x: the same of the output statement x: for no further witness both R0's relation holds at
   the
   caller's statement a and the lookup's out-claim holds of x at the entries read off m.
 - lookOut_total: on every typed transcript the lookup's verifier puts out a statement, with the
   caller's
   state in it and the oracles unchanged.
 - lookPeel: under NoIn the prover has lost in s ++ t towards a goal, with the error counts ε', then
   those
   of t, if two debts are paid in t alone:
     noImage: after every transcript of s without an image;
     noOut: after every transcript of s whose image leads the typed verifier to a statement x with
       NoOut.
 - lookBack_know: the typed lookup read on the written rounds (backS) is round-by-round knowledge
   sound
   between the lookup's own two relations, with the error counts ε'.
 - kfTrue, NoClaims, noClaims_of_noOut: NoOut in the flat function's words: for no further witness
   both R0's relation holds and all values of Fo.claimsOf are 0, at the plain data of the image,
   with the keys' letter at the multilinear extension of each call's own key vector, read off m, at
   the flat function's point for that call.
 - lookPeel_claims: lookPeel with the second debt in these words.

Premises besides: in lookPeel and lookPeel_claims R0's condition holds at the caller's statement a;
in noClaims_of_noOut and lookPeel_claims 5 ≤ lm ≤ kT + 5, and the layout lays mask entry s at
mk (jLK + s) and the cells by pl.
Limits. lookBack_know says nothing of a written transcript without an image: there the reduction
read on the written rounds refuses. F, ε', s, t and the goal are parameters: no written round is
named here. The two debts are
hypotheses. The first is a debt on the goal: the error counts ε' count written verifier messages
with an image alone, so a written transcript without an image (a failed test of work) must be one of
which the goal holds, whatever follows. NoClaims names no form of the byte-level verifier: that a
key form of its has the value kfTrue is what the caller's later rounds are to show. Nothing here
ties the image of a written transcript to what the byte-level verifier
hears.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Flat.CarrySkip
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import OnBytes.Tie.Pv.Lookup.Forest.FoClaims
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKOut

set_option autoImplicit false

namespace Fo
open Iop Prob IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole TwV Cb.Fo.NumsEq Cb.Fo.Pin OnBytes.Slice
open OnBytes.Flat

/-- One block is taken off the front, along maps that may skip written rounds. -/
theorem peelS {A B WA WB : Type} (K : Reduction A B) {on : A → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (hK : K.Know on RA RB ext ε) (a : A) (ha : on a) (hno : ∀ w, ¬ RA a w) {s t : Shape}
    (F : CarryS s K.shape) (ε' : Err s) (hF : F.Fits ε ε') (ε₂ : Err t)
    (bad : Tr (s ++ t) → Prop)
    (h0 : ∀ τ, F.tr τ = none → Doomed t ε₂ fun b => bad (Tr.app τ b))
    (hT : ∀ τ τ', F.tr τ = some τ' → (∀ b w, K.out a τ' = some b → ¬ RB b w) →
      Doomed t ε₂ fun b => bad (Tr.app τ b)) :
    Doomed (s ++ t) (Err.app ε' ε₂) bad :=
  Doomed.append s t _ ε₂ bad
    (CarryS.doomed F ε ε' hF _
      (fun τ' => ∀ b w, K.out a τ' = some b → RB b w → RA a (ext a τ' w)) h0
      (fun τ τ' hτ hb => hT τ τ' hτ fun b w hout hw => hno _ (hb b w hout hw)) (hK a ha))

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay Cb.Gl.E St₀ J₀)
  {Ex : ExtSpec} {Kc M Wp : Type} (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) (m : M)

/-- The lookup's input statement has no witness at the committed messages m. -/
def NoIn (a : St₀ × Ex.Str) : Prop := ∀ wp, ¬ (forIn Cb.Gl.E h L R0 msg₀).relR a (m, wp)

/-- The lookup's output statement has no witness at m. -/
def NoOut (a : St₀ × Ex.Str) (x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) : Prop :=
  ∀ wp, ¬ (R0.relR a (m, wp) ∧ (forA Cb.Gl.E h L).lk.out id id x (zext (msg₀ m)))

/-- The typed verifier never refuses; the caller's state and the oracles are handed on. -/
theorem lookOut_total (a : St₀ × Ex.Str) (τ : Tr (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) :
    ∃ x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀),
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧ x.1.1 = a.1 := by
  have e := Tw.allK₀_out Ex (forA Cb.Gl.E h L) (forP Cb.Gl.E h L) (FoNums.several h) a τ
  exact ⟨_, e, congrArg Prod.fst
    (Tw.allK₀_st Ex (forA Cb.Gl.E h L) (forP Cb.Gl.E h L) (FoNums.several h) a τ _ e).1⟩

/-- **The lookup is taken off the front.** -/
theorem lookPeel (H : FoNums.ok h = true) (a : St₀ × Ex.Str) (ha : R0.on a)
    (hno : NoIn h L R0 msg₀ m a) {s t : Shape}
    (F : CarryS s (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) (ε' : Err s)
    (hF : F.Fits (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e ε') (ε₂ : Err t)
    (bad : Tr (s ++ t) → Prop)
    (noImage : ∀ τ, F.tr τ = none → Doomed t ε₂ fun b => bad (Tr.app τ b))
    (noOut : ∀ τ τ' x, F.tr τ = some τ' →
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a τ' = some (x, a.2) →
      NoOut h L R0 msg₀ m a x → Doomed t ε₂ fun b => bad (Tr.app τ b)) :
    Doomed (s ++ t) (Err.app ε' ε₂) bad :=
  peelS (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red
    ((holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H).know m) a ha hno F ε' hF ε₂ bad noImage
    fun τ τ' hτ hb => by
      obtain ⟨x, hx, hst⟩ := lookOut_total h L a τ'
      refine noOut τ τ' x hτ hx fun wp hw => hb (x, a.2) wp hx ⟨?_, hw.2⟩
      show R0.relR (x.1.1, a.2) (m, wp)
      rw [hst]
      exact hw.1

/-- The typed lookup, read on the written rounds, is knowledge sound. -/
theorem lookBack_know (H : FoNums.ok h = true) {A : Type} {s : Shape}
    (F : A → CarryS s (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) (ε' : Err s)
    (hF : ∀ a, (F a).Fits (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e ε') (fa : A → St₀ × Ex.Str)
    (tr₀ : Tr (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) :
    (backS (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red F fa).Know (fun a => R0.on (fa a))
      (fun a wp => (forIn Cb.Gl.E h L R0 msg₀).relR (fa a) (m, wp))
      (fun b wp => (forOut Cb.Gl.E h L R0 msg₀).relR b (m, wp)) (fun _ _ wp => wp) ε' :=
  backS_know _ F _ ε' hF fa _ _ _ _ tr₀ ((holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H).know m)

/-- The multilinear extension of call c's key vector, read off m, at the point that the flat
function
has for that call at the plain data rs. -/
def kfTrue (a : St₀ × Ex.Str) (lm jLK : ℕ) (rs : Rounds Cb.Gl.E) (c : ℕ) : Cb.Gl.E :=
  extL (forK Cb.Gl.E L a.1 (zext (msg₀ m)) c) ((endsOf h lm jLK rs).zk.getD c [])

/-- For no further witness both the caller's relation holds and all values of the flat function's
claims are 0, at the plain data rs, the keys' letter at the key vectors' own extensions. -/
def NoClaims (a : St₀ × Ex.Str) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (rs : Rounds Cb.Gl.E) : Prop :=
  ∀ wp, ¬ (R0.relR a (m, wp) ∧
    ∀ y ∈ claimsOf h lm jLK rs (fun p => zext (msg₀ m) (placeOf mk pl p))
      (colsK h lm (endsOf h lm jLK rs).zb0 fun p => zext (msg₀ m) (placeOf mk pl p))
      (colsK h lm (endsOf h lm jLK rs).zb1 fun p => zext (msg₀ m) (placeOf mk pl p))
      (pinColK lm fun p => zext (msg₀ m) (placeOf mk pl p))
      (kfTrue h L msg₀ m a lm jLK rs), y = 0)

/-- An output statement without a witness, in the flat function's words. -/
theorem noClaims_of_noOut (H : FoNums.ok h = true) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2)
    (a : St₀ × Ex.Str) (τ' : Tr (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape)
    (x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
    (hx : (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a τ' = some (x, a.2))
    (hN : NoOut h L R0 msg₀ m a x) :
    NoClaims h L R0 msg₀ m a lm jLK mk pl (forFl h L Ex τ') := fun wp hw => by
  obtain ⟨x', hx', hI⟩ := hcClaims Cb.Gl.E St₀ J₀ h L lm jLK mk pl H h5 hlm hmk hbc Ex a τ'
  obtain rfl : x' = x := congrArg Prod.fst (Option.some.inj (hx'.symm.trans hx))
  refine hN wp ⟨hw.1, (hI (fun c => AffK.ofConst (kfTrue h L msg₀ m a lm jLK (forFl h L Ex τ') c))
    (msg₀ m) (fun c _ => AffK.val_ofConst _ _)).2 ?_⟩
  have e : (fun c => AffK.val (AffK.ofConst (kfTrue h L msg₀ m a lm jLK (forFl h L Ex τ') c) :
      AffK (Option J₀) Cb.Gl.E) (zext (msg₀ m))) = kfTrue h L msg₀ m a lm jLK (forFl h L Ex τ') :=
    funext fun c => AffK.val_ofConst _ _
  rw [e]
  exact hw.2

/-- The second debt in the flat function's words. -/
theorem lookPeel_claims (H : FoNums.ok h = true) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2)
    (a : St₀ × Ex.Str) (ha : R0.on a) (hno : NoIn h L R0 msg₀ m a) {s t : Shape}
    (F : CarryS s (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) (ε' : Err s)
    (hF : F.Fits (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e ε') (ε₂ : Err t)
    (bad : Tr (s ++ t) → Prop)
    (noImage : ∀ τ, F.tr τ = none → Doomed t ε₂ fun b => bad (Tr.app τ b))
    (noClaims : ∀ τ τ', F.tr τ = some τ' →
      NoClaims h L R0 msg₀ m a lm jLK mk pl (forFl h L Ex τ') →
      Doomed t ε₂ fun b => bad (Tr.app τ b)) :
    Doomed (s ++ t) (Err.app ε' ε₂) bad :=
  lookPeel h L R0 msg₀ m H a ha hno F ε' hF ε₂ bad noImage fun τ τ' x hτ hx hN =>
    noClaims τ τ' hτ
      (noClaims_of_noOut h L R0 msg₀ m H lm jLK mk pl h5 hlm hmk hbc a τ' x hx hN)

end

end Fo
