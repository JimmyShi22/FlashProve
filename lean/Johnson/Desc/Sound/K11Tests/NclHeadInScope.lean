-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/NclHeadInScope.lean: THE TEST WITH CODE nclB Z 24 1
(Johnson/Top/H0/MergeLaw/PlanNclAt.lean: "the planner has a link number 24, and it states one claim
on the committed table") SAYS YES AT ALL PUBLIC FILES IN THE GOALS' SCOPE. It is the field oneClaim
of the named condition for the merge of the claims on the committed table (kind K11).
Statements and proofs; nothing is evaluated at particular files.

  planH2_ncl            where Head.planH2 returns a plan, its field NCL is 1: the routine lays the
                        literal
  public_H_ncl          so X.H.NCL = 1 at everything that publicOf returns: NO SCOPE
  nclB_head_of_public   the test, in scope, where Z is the plain road's public part and publicOf
                        returns Z.p.X
  nclB_head_in_scope    the same with "the blank ground is there" in the last premise's place: the
                        four premises of IM.ground_tails (Johnson/IMR/K8Seat.lean)

How. Z.p.built is what buildLinksH returns at the plain list of links (IM.planned_built,
IM.plain_built); its links are the given ones with arrayOf filled (Meaning.built_at); in scope there
are twelve groups with attention (Meaning.scope_plans), so the list's link number 24 is the output
head's (listLinksH_with), whose NCL is the head's plan's.
The scope is spent for "twelve groups, with attention" alone.

Limits. That the premises can be met together is not shown here. Nothing on a verifier's state.
Nothing on soundness.

-/
import Johnson.IMR.PureJoin
import Johnson.Top.H0.MergeLaw.PlanNclAt
import Johnson.Goal.Meaning.PlanShapes
import OnBytes.Tie.Pv.Tail.EndHeadForms
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc.First.MergeLaw (nclB)

open OnBytes.Tie.Pv.Tail.Port (excBind_ok throw_bind_ne) in
/-- **The output head's plan states one claim on the committed table**: the routine's literal. -/
theorem planH2_ncl (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (h : Head.planH2 g hS Lh b O NGr lkW = .ok hp) : hp.NCL = 1 := by
  unfold Head.planH2 at h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tl0, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨⟨tla, Fa, Ta⟩, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlF, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    rfl
  · exact absurd h (throw_bind_ne _ _ _)

/-- At everything that publicOf returns. -/
theorem public_H_ncl {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) : X.H.NCL = 1 := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H h
  have e : X.H.NCL = H0.NCL := by rw [h2]
  exact e.trans (planH2_ncl _ _ _ _ _ _ _ _ h1)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}

/-- **THE TEST SAYS YES IN SCOPE.** -/
theorem nclB_head_of_public (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X) : nclB Z 24 1 = true := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts P.pol lay P.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  unfold ProofFile.Plain.linksPlain at h₀
  rw [hq, hN] at h₀ hB
  obtain ⟨-, -, -, -, e0⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨ar, e⟩ := (Meaning.built_at hB).2 24 _ e0
  unfold nclB
  rw [e]
  exact decide_eq_true (congrArg some (public_H_ncl hX))

/-- The same, at the four premises of IM.ground_tails. -/
theorem nclB_head_in_scope {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) : nclB Z 24 1 = true :=
  nclB_head_of_public hS hR hZ (by
    rw [← ProofFile.Law.blankBy_W hG]
    exact IM.ground_publicK hZ hG)

end

end LT28.K11Tests

#print axioms LT28.K11Tests.planH2_ncl
#print axioms LT28.K11Tests.public_H_ncl
#print axioms LT28.K11Tests.nclB_head_of_public
#print axioms LT28.K11Tests.nclB_head_in_scope
