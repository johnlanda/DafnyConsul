include "base.dfy"

module def.core {
    import opened base

    datatype PatElem = Star | JustChar(char)

    type Pattern = seq<PatElem>

    type EntityUID = string

    datatype Primitive =
        Bool(b: bool) |
        Int(i:int) |
        String(s: string) |
        EntityUID(s: EntityUID)

    datatype Value =
        Primitive(primitive: Primitive) |
        Set(s: set<Value>) |
        Record(record: Record)
    {
        static function Bool(b: bool): Value {
            Primitive(Primitive.Bool(b))
        }
        static const TRUE := Bool(true)
        static const FALSE := Bool(false)

        static function Int(i: int): Value {
            Primitive(Primitive.Int(i))
        }

        static function String(s: string): Value {
            Primitive(Primitive.String(s))
        }

        static function EntityUID(uid: EntityUID): Value {
            Primitive(Primitive.EntityUID(uid))
        }

        static function asBool(v: Value): Result<bool> {
            match v {
                case Primitive(Bool(b)) => Ok(b)
                case _ => Err(TypeError)
            }
        }

        static function asEntity(v: Value): Result<EntityUID> {
            match v {
                case Primitive(EntityUID(e)) => Ok(e)
                case _ => Err(TypeError)
            }
        }

        static function asSet(v: Value): Result<set<Value>> {
            match v {
                case Set(s) => Ok(s)
                case _ => Err(TypeError)
            }
        }

        static function asRecord(v: Value): Result<Record> {
            match v {
                case Record(r) => Ok(r)
                case _ => Err(TypeError)
            }
        }
    }

    type Attr = string
    type Record = map<Attr, Value>

    datatype Var = Source | SourceNamespace | Destination | DestinationNamespace

    datatype BinaryOp = Eq

    datatype Expr =
        PrimitiveLit(Primitive) |
        Var(Var) |
        And(Expr, Expr) |
        BinaryApp(BinaryOp, Expr, Expr) |
        Record(fvs: seq<(Attr, Expr)>)

    datatype Action = Allow | Deny
    
    datatype IntentionID = IntentionID(id: string)

    datatype Intention = Intention(
        action: Action,
        sourceScope: SourceScope,
        sourceNamespaceScope: SourceNamespaceScope,
        destinationScope: DestinationScope,
        destinationNamespaceScope: DestinationNamespaceScope,
        precedence: int) 
    {
        function toExpr(): Expr {
            Expr.And(
                sourceScope.toExpr(),
                Expr.And(
                    sourceNamespaceScope.toExpr(),
                    Expr.And(
                        destinationScope.toExpr(),
                        destinationNamespaceScope.toExpr()
                    )
                )
            )
        }
    }

    datatype SourceScope = SourceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.Source)
        }
    }

    datatype SourceNamespaceScope = SourceNamespaceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.SourceNamespace)
        }
    }

    datatype DestinationScope = DestinationScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.Destination)
        }
    }

    datatype DestinationNamespaceScope = DestinationNamespaceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.DestinationNamespace)
        }
    }

    datatype Scope = Any | Eq(entityUID: EntityUID)
    {
        function toExpr(v: Var): Expr {
            match this {
                // Since we do not allow partial matches we can check for
                // just the Any (*) case or the exact match
                case Any => PrimitiveLit(Primitive.Bool(true))
                case Eq(e) => BinaryApp(BinaryOp.Eq, Var(v), PrimitiveLit(Primitive.EntityUID(e)))
            }
        }
    }

    datatype Request = 
        Request(source: EntityUID,
                sourceNamespace: EntityUID,
                destination: EntityUID,
                destinationNamespace: EntityUID)

    datatype EntityData = EntityData(attrs: Record)

    datatype EntityStore = EntityStore(
        entities: map<EntityUID, EntityData>)
    {
        function getEntity(uid: EntityUID): base.Result<Record> {
            if uid in entities.Keys then
                Ok(entities[uid].attrs)
            else
                Err(EntityDoesNotExist)
        }
    }

    datatype IntentionStore = IntentionStore(intentions: map<IntentionID, Intention>)

    datatype Store = Store(entities: EntityStore, intentions: IntentionStore)
    
    datatype Response = Response(decision: Decision)

    datatype Decision = AllowRequest | DenyRequest
}