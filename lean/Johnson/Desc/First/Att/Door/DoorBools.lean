-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/DoorBools.lean: FOR A FILE OF EVALUATIONS ALONG A WALK: FOUR SMALL Bools ON THE FIRST CHAIN's RECORD, TYPED OUT so that such a file can import them without Mathlib: each IS, BY LEAN (Johnson/Desc/First/Att/Door/Law/DoorTie.lean: rfl), the Bool of which K5's files' lemmas speak: freeFromB | freeAboveB | callerIn3B: Johnson/Desc/First/Att/K05BehindLay3.lean's freeFromB | freeAboveB | k5CallerIn3 · linkFreshB: Johnson/Desc/First/Att/K05BehindLay.lean's.
-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

def freeFromB (s : S) : Bool :=
  s.fork?.any fun G => (List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true

def freeAboveB (nsPlan : Nat) (s : S) : Bool := (s.fork?.any fun G => G.ns == nsPlan) && freeFromB s

def callerIn3B (first : Nat) (s : S) : Bool :=
  match s.here with
  | .att a => a.heard5.isNone && a.g.isSome && a.F.next == first
  | _ => false

def linkFreshB (arr : Array (Nat × String)) (s : S) : Bool :=
  (s.tl?.bind (·.heard)).isNone && s.link?.any fun L => L.arrayOf == arr

end H2K5.Door
