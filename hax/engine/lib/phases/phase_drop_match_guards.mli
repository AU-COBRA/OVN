open! Prelude

module Make (F : Features.T) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.Off.Match_guard
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
