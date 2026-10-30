-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LinksAt.lean: the block of the links of a proof's first chain at an instance, from what
the verifier program itself computes of the three public files.

Definitions, and four equations. p is what `Model.Verify.planned` (OnBytes/Model/Verify.lean)
returns at the three public files. An instance is an `Instance' P` (Johnson/Flat/Instance.lean).

Main names:
  `linksAtWords p request reply`: the block of the links of a proof's first chain at the words of a
    request file and of a reply file. It is the term that the program hands `Proof.check`, step for
    step as the theorem `Shell.main_zero` (OnBytes/Shell/AtWhole.lean) tells it: `Head.stFromCall`,
    `Head.coveredOf`, `Verify.linksOf`, then `Stages.runLinksH` at the links as built, each with the
    check that knows the request.
  `linksOf p x`: the same at the words that say the instance x; a block that fails where one of the
    three steps refuses.
  `replyOf x`: the reply token as an element of the extension field, as the program hands it on.
  `linksAtWords_ok`: at an instance with r < e, and y = 0 if e < P.T, where P.T is p's window, P.T <
    2 ^ 32 and P.V ≤ 2 ^ 32, the first step does not refuse, and `linksAtWords` is the two other
    steps at r, e, y of x. `linksOf_eq`: `linksOf` by cases.
  `common_parts`, `linksAtWords_program`: the public part and the links as built of the stages'
    common beginning are p's; so the block that `Shell.main_zero` names is what `linksAtWords`
    returns at the words of the call's request and reply.
  `firstInstance P hV`: tokens 0, the last position alone covered, the reply 0.
  `withoutReply hV x`: x with the reply 0.
Limits: nothing on a protocol. THAT P IS THE SIZES OF p's PARAMETER FILE IS NOT ASKED HERE, AND IS
LEFT TO THE PLACE OF USE (P := `sizesAt` of that file): at another P.T the first step refuses the
words; P.V is met in the second step alone, token by token against p's; the other eight sizes are
read by no step.

-/
import Johnson.Flat.InstanceLaws
import OnBytes.Model.Verify

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model

/-- The block of the links of a proof's first chain, at the words of a request and of a reply. -/
def linksAtWords (p : Verify.Planned) (request reply : Array UInt32) :
    Except String (Blk Proof.LinksResult) := do
  let so ← Head.stFromCall request reply p.X.T
  let cov ← Head.coveredOf so p.X.T p.X.P.h.V
  let links ← Verify.linksOf p.X cov
  pure (Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
    p.chains.proof.first p.X.layers.wsLay)

/-- The same at the words that say an instance; a block that fails where a step refuses. -/
def linksOf (p : Verify.Planned) {P : Params} (x : Instance' P) : Blk Proof.LinksResult :=
  match linksAtWords p (requestWordsOf x) (replyWordsOf x) with
  | .ok b => b
  | .error name => Blk.fail name

/-- `linksOf` by cases. -/
theorem linksOf_eq (p : Verify.Planned) {P : Params} (x : Instance' P)
    {b : Blk Proof.LinksResult} (h : linksAtWords p (requestWordsOf x) (replyWordsOf x) = .ok b) :
    linksOf p x = b := by
  unfold linksOf
  rw [h]

/-- At an instance that the reader takes, `linksAtWords` is the two other steps at its numbers. -/
theorem linksAtWords_ok (p : Verify.Planned) {P : Params} (x : Instance' P) (hP : P.T = p.X.T)
    (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32) (hre : x.r < x.e) (hy : x.e < P.T → x.y.val = 0) :
    linksAtWords p (requestWordsOf x) (replyWordsOf x) =
      (do
        let cov ← Head.coveredOf { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val }
          p.X.T p.X.P.h.V
        let links ← Verify.linksOf p.X cov
        pure (Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
          p.chains.proof.first p.X.layers.wsLay)) := by
  unfold linksAtWords
  rw [← hP, stFromCall_wordsOf x hT hV hre hy]
  rfl

/-- What the stages' common beginning holds of the public part and of the links as built is what
`Verify.planned` has returned. -/
theorem common_parts {r : Verify.Read} {p : Verify.Planned} {C : Verify.Common}
    (hp : Verify.planned r.pol r.KL r.layout = .ok p) (hC : Verify.commonOfCall r = .ok C) :
    C.X = p.X ∧ C.built = p.built ∧ C.chains = p.chains := by
  unfold Verify.commonOfCall at hC
  rw [hp] at hC
  have h : Verify.commonOf p.X p.cfg p.chains p.built r.key r.id.asked = .ok C := hC
  unfold Verify.commonOf at h
  cases hk : Key.readTable p.chains.tableShape p.cfg r.key with
  | error e =>
    rw [hk] at h
    cases h
  | ok t =>
    rw [hk] at h
    by_cases hb : (!r.id.asked.isEmpty &&
        r.id.asked != Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg t.1)) = true
    · simp [Verify.named, Model.refuseIf, hb, Except.mapError, bind, Except.bind, pure,
        Except.pure] at h
    · simp [Verify.named, Model.refuseIf, hb, Except.mapError, bind, Except.bind, pure,
        Except.pure] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

/-- **The block that the program hands `Proof.check` is `linksAtWords`.** If the four steps that
`Shell.main_zero` tells of went through at the stages' common beginning C, then `linksAtWords` at p
returns the block that the theorem names. -/
theorem linksAtWords_program {r : Verify.Read} {p : Verify.Planned} {C : Verify.Common}
    (hp : Verify.planned r.pol r.KL r.layout = .ok p) (hC : Verify.commonOfCall r = .ok C)
    {so : Head.StOwn} {cov : Head.Covered} {links : Array Stages.LinkH}
    (h1 : Head.stFromCall (Verify.words32 r.request) (Verify.words32 r.y) C.X.T = .ok so)
    (h2 : Head.coveredOf so C.X.T C.X.P.h.V = .ok cov) (h3 : Verify.linksOf C.X cov = .ok links) :
    linksAtWords p (Verify.words32 r.request) (Verify.words32 r.y) =
      .ok (Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
        p.chains.proof.first C.X.layers.wsLay) := by
  obtain ⟨hX, hB, _⟩ := common_parts hp hC
  rw [hX] at h1 h2 h3
  unfold linksAtWords
  simp only [h1, h2, h3, hX, hB, bind, Except.bind, pure, Except.pure]

/-- The reply token as an element of the extension field. -/
def replyOf {P : Params} (x : Instance' P) : E := ofNat x.y.val

/-- Tokens 0, the last position alone covered, the reply 0. -/
def firstInstance (P : Params) (hV : 0 < P.V) : Instance' P :=
  Instance.nextOf (fun _ => ⟨0, hV⟩) ⟨0, hV⟩

/-- The instance with the reply 0. -/
def withoutReply {P : Params} (hV : 0 < P.V) (x : Instance' P) : Instance' P :=
  { x with y := ⟨0, hV⟩ }

end OnBytes.Flat
