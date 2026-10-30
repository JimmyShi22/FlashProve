-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadKind.lean: THE OUTPUT HEAD'S OWN ROUNDS (Head.lean) as a kind of block: the
record of Johnson/Desc/Block.lean, filled from Head.lean's text through HeadFrame.lean. With its
fields under names of their own, for tests: each is read off the kind: no second text. Definitions
with code; no theorem.

-/
import Johnson.Desc.Kinds.HeadRow
import Johnson.Desc.Kinds.HeadFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

variable {S : Type}

/-- THE KIND. S: the carried record; L: what the kind reads of it and lays into it. Cl: the type of
a claim, a letter; cl: from a form. link, piece: where the place stands in the first chain. p: the
place's public parameters, numbers of the plan alone. No round sends a root, so no round has an
oracle; the block is owed no column. -/
def kind {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) : Kind Par S Cl := fun p =>
  let rs := p.declare (let _ := p.sizes; rounds)
  { name := "the output head's own rounds", place := ⟨1, some link, piece, outputHead⟩
    planOk := p.ok, rounds := rs, oracles := rs.map fun _ => [], before := p.before
    decide := fun s v _ =>
      decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s v
    claims := runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl p L
    after := [] }

/-- ROUNDS, as the plan's declared rounds. -/
def Par.rounds (p : Par) : List Fmt.DeclaredRound :=
  let _ := p.sizes
  p.declare Head.rounds

/-- DECIDES. -/
def decide (p : Par) (L : Seat S) (s : S) (rs : List Fmt.RoundView) : Except String S :=
  (kind (Cl := Form) id L 0 0 p).decide s rs []

/-- CLAIMS. -/
def runs {Cl : Type} (toCl : Form → Cl) (p : Par) (L : Seat S) :
    List (String × (Nat → S → Except String (List Cl × S))) :=
  (kind toCl L 0 0 p).claims

/-- The key vector of a call: `keyVector` (HeadFrame.lean) at the head's `key` (Head.lean). -/
abbrev keyForm [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
    [Heard] [FinalNorm.Reads] [Reads] (padding : OnBytes.E) (keys : List PlaceKey) : Form :=
  keyVector key padding keys

/-- The guests, as a host takes them: they borrow zt: the last lt coordinates of the lookup's point,
here numbered from 0, with degree 1 in each. form needs the reads' places and what was
heard, which lie behind the host's last draw. -/
def guestsOf {Cl : Type} (toCl : Form → Cl) (p : Par) (L : Seat S) : List (GuestOf S Cl) :=
  let _ := p.sizes
  ["clip", "table"].map fun name =>
    { name, coords := (List.range Norm.lt).map fun i => (i, 1)
      form := fun s => (lettersAt p L s).bind fun (_, _, _) =>
        named "the guest is there" ((guests.lookup name).map toCl) }

end VerifiableInference.Desc.Kinds.Head
