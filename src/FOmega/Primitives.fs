namespace Nemonuri.TypeSystems.FOmega.Primitives


[<RequireQualifiedAccess>]
module Kinds = begin

    type IKind = interface end

    type Star = struct
        interface IKind
    end

    type Arrow<'p, 'q when 'p :> IKind and 'q :> IKind> = struct
        interface IKind
    end

end

[<RequireQualifiedAccess>]
module Canons = begin

    module K = Kinds

    type ICanon<'kind when 'kind :> K.IKind> = interface end

    type Star<'a> = struct
        interface ICanon<K.Star>
    end

    type Arrow<'pk, 'pc, 'qk, 'qc
                when 'pk :> K.IKind and 'pc :> ICanon<'pk>
                and 'qk :> K.IKind and 'qc :> ICanon<'qk>> = struct
        interface ICanon<K.Arrow<'pk, 'qk>>
    end

end

