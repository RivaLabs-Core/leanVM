import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

def zeroForgery : Forgery :=
  ⟨0, ⟨0, fun _ => 0, fun _ _ => 0, fun _ => ⟨0, fun _ => 0, fun _ => 0⟩⟩⟩

end SphincsSecurity.Concrete
