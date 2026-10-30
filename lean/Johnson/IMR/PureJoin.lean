-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/PureJoin.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
 A LAW ABOUT ProofFile.onlineDescriptionFromPublicPart AND ProofFile.baseOf: what the description onlineDescription
   (Johnson/Desc/ProofFile/OnlineDescription.lean) hands its lots is the public part's own record, and its
   list of links is the list of
which Meaning/PlanShapes.lean and Meaning/PlanNames.lean speak; and onlineDescriptionFromPublicPart's and baseOf's texts, opened.
OBJECT. ProofFile.onlineDescription · ProofFile.pubPlain · ProofFile.blankBy ProofFile.pureRoad.links · ProofFile.baseOf · ProofFile.onlineDescriptionFromPublicPart. USER. Every seat (IM/…); the scope's lemmas (base_made · pure_chain).
LETTERS. o: the second hash function as a letter · Z: pubPlain's value · G₀: the blank letters ·
B: baseOf's record.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).
The laws of ProofFile that this file needs, in Johnson/Desc/ProofFile/Law/MakerPublic.lean, are called here, not written again.
blank_ground's clause «G₀.W = Z.p.X» is ProofFile.Law.blankBy_W's too: it stays as a clause of a longer statement.

  orSay_ok · planned_built · plain_built   what the plain road's makers have called behind the public record, by their texts.
  blank_ground      the blank letters on the pure road: W := Z.p.X, built := zipped Z.p.built ls, where ls is what linksPlain returns; first := Z.first.
  base_made         what baseOf has made: the places · the shape · the blank letters · every lot's table at these.
  pure_base · pure_ground · pure_chain   where onlineDescriptionFromPublicPart returns F: baseOf has returned B; THE SEAT HAS NO FAULT AND LACKS NOTHING (faultsAt T B = [] · lackingAt T (partsAt T B) = []); the list base and the chain c of chainBy are there; T.shared = some A ·
                    T.second = some B'; F is fileDescBy T.older T.links Z A B' … c.
  ground_public     THE JOIN, AT EVERY o: where pubPlain o returns Z and the blank letters are G₀: publicOfO o pol KL (some lay) = ok G₀.W, and G₀.built = zipped B ls at l₀, B, ls made by listLinksH … and buildLinksH ….
  ground_publicK    at OnBytes.secondHashFunction: publicOf pol KL (some lay) = ok G₀.W.
  ground_gets · ground_named   so, in the goals' scope, AT secondHashFunction: G₀.built has 25 links; the rule getsAt G₀.W gives each its records getsOf G₀.W k; the kinds, groups, names, identifiers and flags are links_named's.

What is not claimed. Nothing on which block sits at which place. Nothing on the letters of a request: the lots of onlineDescription are made at the blank letters alone. Nothing in scope at an o other than secondHashFunction. No soundness.
-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.Meaning.PlanNames

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped ok_bind)

/-! ## 1 The makers' texts -/

theorem orSay_ok {α : Type} {w : String} {x : Option α} {a : α}
    (h : ProofFile.orSay w x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some b => exact congrArg some (Except.ok.inj h)

/-- What the plain planned has called behind the public record (the record itself: ProofFile's own ProofFile.Law.planned_public). -/
theorem planned_built {pol KL : ByteArray} {lay : Option ByteArray} {p : Verify.Planned}
    (h : ProofFile.Plain.planned o pol KL lay = .ok p) : ProofFile.Plain.builtOf p.X p.chains = .ok p.built := by
  unfold ProofFile.Plain.planned at h
  obtain ⟨X, _, h⟩ := ok_bind h
  obtain ⟨chains, _, h⟩ := ok_bind h
  obtain ⟨built, hb, h⟩ := ok_bind h
  cases h
  exact hb

/-- What the plain builtOf has called. -/
theorem plain_built {X : Verify.Public} {c : Verify.Chains} {B : LinksH}
    (h : ProofFile.Plain.builtOf X c = .ok B) :
    ∃ l₀, ProofFile.Plain.linksPlain X = .ok l₀ ∧
      buildLinksH l₀ X.NGr X.p4 X.layers.wsLay c.proof.first = .ok B := by
  unfold ProofFile.Plain.builtOf at h
  exact ok_bind h

/-! ## 2 The blank letters -/

/-- **The blank letters on the pure road.** -/
theorem blank_ground {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (h : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∃ ls, ProofFile.Plain.linksPlain Z.p.X = .ok ls ∧ G₀.W = Z.p.X ∧ G₀.built = zipped Z.p.built ls ∧
      G₀.first = Z.first := by
  unfold ProofFile.blankBy at h
  dsimp only at h
  generalize hs : Z.s₀.withReq _ = s at h
  cases hL : ProofFile.lettersBy ProofFile.pureRoad.links Z s with
  | error e =>
    rw [hL] at h
    cases h
  | ok G =>
    rw [hL] at h
    obtain rfl : G = G₀ := Option.some.inj h
    unfold ProofFile.lettersBy at hL
    dsimp only at hL
    split at hL
    all_goals
      obtain ⟨cov, _, hL⟩ := ok_bind hL
      obtain ⟨ls, hl, hL⟩ := ok_bind hL
      cases hL
      exact ⟨ls, hl, rfl, rfl, rfl⟩

/-! ## 3 Where onlineDescription returns -/

/-- **What baseOf has made**: the places, the shape, the blank letters, every lot's table at these. -/
theorem base_made {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (h : ProofFile.baseOf Z T = .ok B) :
    ProofFile.spotsOf Z.cuts = some B.spots ∧ ProofFile.shapeOf Z = .ok B.shape ∧
      ProofFile.blankBy T.links Z = some B.G₀ ∧ B.all = T.lots.map fun L => (L, L.blocks B.G₀) := by
  unfold ProofFile.baseOf at h
  obtain ⟨ps, h1, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨sh, h2, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨G, h3, h⟩ := ProofFile.Law.exBind_ok h
  cases h
  exact ⟨orSay_ok h1, h2, orSay_ok h3, rfl⟩

/-- Where onlineDescriptionFromPublicPart returns, baseOf has returned. -/
theorem pure_base {Z : ProofFile.Pub} {T : ProofFile.PureSeat}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ B, ProofFile.baseOf Z T = .ok B := by
  unfold ProofFile.onlineDescriptionFromPublicPart at h
  obtain ⟨B, hB, -⟩ := ProofFile.Law.exBind_ok h
  exact ⟨B, hB⟩

/-- Where onlineDescriptionFromPublicPart returns, the blank letters are made. -/
theorem pure_ground {Z : ProofFile.Pub} {T : ProofFile.PureSeat}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ G₀, ProofFile.blankBy T.links Z = some G₀ := by
  obtain ⟨B, hB⟩ := pure_base h
  exact ⟨B.G₀, (base_made hB).2.2.1⟩

/-- **Where onlineDescriptionFromPublicPart returns: the base, no fault, nothing lacking, the places' blocks, the chain, the two later seats.** -/
theorem pure_chain {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (B : ProofFile.PureBase) (base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl))
        (c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl) (A : ProofFile.SharedSeat)
        (B' : ProofFile.SecondSeat),
      ProofFile.baseOf Z T = .ok B ∧ ProofFile.faultsAt T B = [] ∧ ProofFile.lackingAt T (ProofFile.partsAt T B) = [] ∧
      (ProofFile.partsAt T B).base = .ok base ∧
      ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c ∧
      T.shared = some A ∧ T.second = some B' ∧
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c := by
  unfold ProofFile.onlineDescriptionFromPublicPart at h
  obtain ⟨B, hB, h⟩ := ProofFile.Law.exBind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      unfold ProofFile.onlineDescriptionAfterTests at h
      obtain ⟨base, hb, h⟩ := ProofFile.Law.exBind_ok h
      obtain ⟨c, hc, h⟩ := ProofFile.Law.exBind_ok h
      split at h
      · rename_i A B' hA hB'
        exact ⟨B, base, c, A, B', hB, by simpa using hf, by simpa using hl, hb, hc, hA, hB',
          (Except.ok.inj h).symm⟩
      · cases h

/-! ## 4 The join -/

/-- **THE JOIN, AT EVERY o: the lots' W is publicOfO o's X, and their list of links is a list of the library's two functions listLinksH and buildLinksH.** -/
theorem ground_public {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok G₀.W ∧
      ∃ (G A : Array SubPlanH) (H : SubPlanH) (l₀ ls : Array LinkH) (B : LinksH),
        listLinksH G₀.W.NGr G₀.W.p4 G A H = .ok l₀ ∧
        buildLinksH l₀ G₀.W.NGr G₀.W.p4 G₀.W.layers.wsLay Z.first = .ok B ∧
        listLinksH G₀.W.NGr G₀.W.p4 G A H = .ok ls ∧ G₀.built = zipped B ls := by
  have hX := ProofFile.Law.pub_public (show ProofFile.pureRoad.pub o pol lay KL = .ok Z from hZ)
  have hB := planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := plain_built hB
  obtain ⟨ls, hl, eW, eB, -⟩ := blank_ground hG
  rw [eW]
  exact ⟨hX, _, _, _, l₀, ls, Z.p.built, h₀, hB, hl, eB⟩

/-- At the second hash function publicOfO is publicOf (publicOfO_older): there the library's laws over publicOf can be spent. -/
theorem ground_publicK {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) : publicOf pol KL (some lay) = .ok G₀.W := by
  rw [← VerifiableInference.PlanWritten.publicOfO_older]
  exact (ground_public hZ hG).1

/-- **In the goals' scope: 25 links, each with its records of the public part.** -/
theorem ground_gets {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    G₀.built.size = 25 ∧
      ∀ k < 25, (G₀.built[k]?).bind (Meaning.getsAt G₀.W) = Meaning.getsOf G₀.W k ∧
        (Meaning.getsOf G₀.W k).isSome = true := by
  obtain ⟨-, G, A, H, l₀, ls, B, h₀, hB, hl, eB⟩ := ground_public hZ hG
  have hX := ground_publicK hZ hG
  rw [eB]
  exact Meaning.links_get' hS hR hX h₀ hB hl

/-- **In the goals' scope: the links' kinds, groups, names, identifiers and flags.** -/
theorem ground_named {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    (∀ g < 12, ∃ l l', G₀.built[2 * g]? = some l ∧ l.kind = 0 ∧ l.g = g ∧
        Meaning.IsNamed l ("G" ++ toString g) (1 + g) true ∧
        G₀.built[2 * g + 1]? = some l' ∧ l'.kind = 1 ∧ l'.g = g ∧
        Meaning.IsNamed l' ("A" ++ toString g) (2 + 12 + g) false) ∧
      ∃ l, G₀.built[24]? = some l ∧ l.kind = 2 ∧ Meaning.IsNamed l "H" (1 + 12) true := by
  obtain ⟨-, G, A, H, l₀, ls, B, h₀, hB, hl, eB⟩ := ground_public hZ hG
  have hX := ground_publicK hZ hG
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  rw [hq, hN] at h₀ hB hl
  obtain ⟨-, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB hl
  obtain ⟨nam, m24, f24, N24⟩ := Meaning.links_named h₀ hB hl
  rw [eB]
  refine ⟨fun g hg => ?_, l24, e24, I24.kind, ?_⟩
  · obtain ⟨s, a, l, l', -, -, e, I, e', I'⟩ := alt g hg
    obtain ⟨m, m', f, N, f', N'⟩ := nam g hg
    obtain rfl : m = l := Option.some.inj (f.symm.trans e)
    obtain rfl : m' = l' := Option.some.inj (f'.symm.trans e')
    exact ⟨m, m', e, I.kind, I.g, N, e', I'.kind, I'.g, N'⟩
  · obtain rfl : m24 = l24 := Option.some.inj (f24.symm.trans e24)
    exact N24

end IM

#print axioms IM.ground_public
#print axioms IM.ground_publicK
#print axioms IM.ground_gets
#print axioms IM.ground_named
#print axioms IM.pure_ground
#print axioms IM.base_made
#print axioms IM.pure_chain
