import SphincsSecurity.Statement
import SphincsSecurity.Completeness
import SphincsSecurity.Proof.Adversary.Security
import SphincsSecurity.Completeness.Assembly

namespace SphincsSecurity

/-- The SPHINCS scheme has 127 bits of classical security (SUF-CMA in the ROM). -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Security.security127

/-- A signature the SPHINCS signer produces verifies, under every hash function. -/
theorem sphincs_is_correct : SphincsCorrectnessStatement :=
  Completeness.correct

/-- The sum of honest-run failure probabilities over all messages is at most `2⁻²⁵⁶`. -/
theorem sphincs_is_complete : SphincsCompletenessStatement :=
  Completeness.complete

/-! The build checks that the public proofs use only Lean's three standard axioms. -/

/-- info: 'SphincsSecurity.sphincs_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_has_127_bits_of_classical_security

/-- info: 'SphincsSecurity.sphincs_is_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_correct

/-- info: 'SphincsSecurity.sphincs_is_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_complete

end SphincsSecurity
