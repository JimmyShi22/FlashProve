-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TellsAtBlocks.lean: the two premises `TieOnOk` and `TieTells` of `ProofSoundOfBlocks`
(Johnson/Flat/ProofOfBlocks.lean) AT THE FILLING THAT IS MEANT: the condition at the first chain's
first boundary holds of the first statement of every instance that passes the description's test on
the instance; the relation there, AT A FIRST STATEMENT, gives `firstRel`
(Johnson/Flat/TiesSheet.lean), read off the public part that the first record holds. Statements,
written as `def … : Prop`, with their proofs; and the law `PutEarly` at the requests that the
program's reader takes.

Why. At the rule of composition's value the first relation reads an instance through the first
record alone, which holds its public part (`Three.ofStarts`, Johnson/Desc/Sound/FileRule.lean).
`TieTells` runs over all instances p and speaks of put p t. So it can be met there only if put reads
p through what the public part keeps: `PutEarly`: put (early p) t = put p t. At the requests, a
subtype at which put has a second arm, that holds in both arms (`putReq_early`): where the second
arm is reached, e is before the window's end, so the request's own reply is 0 and it is its own
early part.

Main names.
  `PutEarly`: put reads an instance through its early part.
  `OnOkAtBlocks`, `onOkAtBlocks`: where the first condition holds of the first statement of every
    instance with `okStart`, and `PubEarly`: `TieOnOk`.
  `TellsAtBlocks`, `tellsAtBlocks`: from `PubKeeps` at the description's own pub
    (Johnson/Flat/TiesFilling.lean), `PutEarly`, and "the relation at the first boundary, at a first
    statement, gives `firstRel` at what back reads off the public part": `TieTells`.
  `putReq_early`, `putEarlyReq`: `PutEarly` at the full size's requests.

Every "there is", walked. None of the statements has one: back is a named function.

BOTH FACTS ARE ASKED AT FIRST STATEMENTS ALONE. Asked of all statements at the
first boundary they cannot be met by a description whose blocks read the public part out of their
own record (a block that is lifted cannot read the copy beside it): there the relation speaks of the
own copy, and the two copies agree at a first record, not at every record. (Found on the way to a
member.)

Limits. THE LOAD MOVES, IT IS NOT CARRIED: with the first relation pinned so, `knows` has to be
shown at it: the first chain's first block's clause must END in `firstRel`: that is where the
meaning sits. `PubKeeps` at the real pub (the request file's bytes; the table's key written of the
record) is a premise: that the key keeps the record whole is shown nowhere here. The small size's
requests: not done.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfBlocks
import Johnson.Flat.TiesAtReq
import Johnson.Desc.Sound.DescRunsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Flat
open Inst.Model OnBytes.Model VerifiableInference.OnPublicFiles.Flat

/-- **put reads a request through its early part**, in both arms. -/
theorem putReq_early (p : Req) (t : Fin ppref.V) : putReq (reqWithoutReply p) t = putReq p t := by
  by_cases h : p.val.e < ppref.T → t.val = 0
  · exact Subtype.ext ((putReq_val (reqWithoutReply p) t h).trans (putReq_val p t h).symm)
  · have he : p.val.e < ppref.T := by
      by_contra hn
      exact h fun h' => absurd h' hn
    have ht : t.val ≠ 0 := fun h0 => h fun _ => h0
    rw [putReq_else (reqWithoutReply p) t he ht, putReq_else p t he ht]
    have hy : p.val.y = ⟨0, ppref_V_pos⟩ := Fin.ext (p.property.2 he)
    refine Subtype.ext ?_
    show { p.val with y := ⟨0, ppref_V_pos⟩ } = p.val
    rw [← hy]

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc.Sound (ThreeAt PlacesAt atDesc atDescFin FinGives rowIOR EAll)

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (all : List LeftT) {X₁ X₂ W : Type} (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Q : PlacesAt (DP.at a) all F W)
  (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)

variable {Tok : Type} (put : Kc.conf.X → Tok → Kc.conf.X) (tok : W → Tok)
  (toW : W → Kc.conf.Cells)

/-- put reads an instance through its early part. -/
def PutEarly : Prop := ∀ p t, put (early p) t = put p t

/-- Where the condition at the first chain's first boundary holds of every FIRST statement (the
first record that an instance's public part gives, a stored table, no tree sent) OF AN INSTANCE THAT
PASSES THE DESCRIPTION's TEST ON THE INSTANCE, AT A STORED TABLE THAT DECODES WITH THE RECORD (so
the condition may hold that promise, which the key file's soundness buys, and hand it on to the
shared chain). The row holds no such test: under the decision's yes it has passed (`runEndIs`,
Johnson/Desc/Sound/DescRunsProofs.lean), and the first record is the same at the early part
(`PubEarly`). -/
def OnOkAtBlocks : Prop :=
  PubEarly Kc early F.pub →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str), F.okStart x = true →
    Kc.conf.D y x.2 ≠ none → Q.on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => []))) →
  TieOnOk Kc DP tFp tJp t3p silP F.run early all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃ (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃)

theorem onOkAtBlocks : OnOkAtBlocks Kc DP tFp tJp t3p silP F early all T g Q h₁ h₂ h₃ := by
  intro hp h x rec y τ ho hD
  rw [wholeIOR_out_eq] at ho
  split at ho
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    have hr : (F.runEnd (x, rec) _ _ _).isOk = true := hc.2
    revert hr
    cases he : F.runEnd (x, rec) _ _ _ with
    | error e => exact fun hr => nomatch hr
    | ok ends =>
      intro _
      obtain ⟨e₁, e₂, e₃⟩ := ends
      have hs := ((VerifiableInference.Desc.Sound.runEndIs _ F (x, rec) _ _ _ e₁ e₂ e₃).1 he).2.1
      have k := h (x, rec) y hs hD
      show Q.on₁ 0 ((F.pub (early x, rec), F.start₁ (F.pub (early x, rec))), (y, fun _ => []))
      rw [hp x rec]
      exact k
  · cases ho

/-- Where the relation at the first chain's first boundary gives `firstRel` at what back reads off
the public part in the record. -/
def TellsAtBlocks (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) : Prop :=
  PubKeeps Kc early F.pub back → PutEarly Kc early put →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) (w : W),
    Q.R₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])) w →
    firstRel Kc DP put tok toW (back (F.pub x), y) w) →
  TieTells Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃
    (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) put tok toW

theorem tellsAtBlocks (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) :
    TellsAtBlocks Kc DP tFp tJp t3p F early all T g Q h₁ h₂ h₃ put tok toW back := by
  intro hk hpe hR p rec y w hw i hi
  have k' : firstRel Kc DP put tok toW (back (F.pub (p, rec)), y) w := hR (p, rec) y w hw
  rw [hk p rec] at k'
  have k'' := k' i hi
  rw [hpe] at k''
  exact k''

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

variable (N : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp))

/-- `PutEarly` at the frame's configuration of the full size at the requests. -/
theorem putEarlyReq : PutEarly (kcReq N pp E) reqWithoutReply putReq := putReq_early

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.putReq_early
#print axioms VerifiableInference.OnPublicFiles.onOkAtBlocks
#print axioms VerifiableInference.OnPublicFiles.tellsAtBlocks
#print axioms VerifiableInference.OnPublicFiles.putEarlyReq
