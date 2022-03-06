open System



#nowarn "62"
#nowarn "40"

module Option =
  let elim
    (none : 'c)
    (some : 'a -> 'c)
    (opt  : 'a option)
          : 'c
    = opt
      |> Option.map some
      |> Option.defaultValue none

/// Lexeme is a class of token.
///
module rec Lexeme =
  
  /// Lexeme is either a concrete token like '(' or ',',
  /// or a category like <num>, <string-literal>, etc.
  ///
  type t =
    | Concrete of token: string
    | Category of klass: string

  let show : Lexeme.t -> string =
    function
    | Concrete t -> "'" + t + "'"
    | Category t -> "<" + t + ">"

/// Terminals to be used in grammar.
///
module rec Term =
  
  /// Terminal is either a normal term or a end-of-file term.
  /// Terminal is not a concrete term, but rather a descriptor of term set.
  ///
  type t =
    | Term of Lexeme.t
    | Eof

  let show : Term.t -> string =
    function
    | Term t -> Lexeme.show t
    | Eof    -> "$"

/// Non-terminals to be used in grammar.
///
module rec NonTerm =
  
  /// Non-terminal is a name of the construct (a left-hand side of any rule),
  /// with separate S for starting rule.
  ///
  type t =
    | NonTerm of string
    | S
  
  let show : NonTerm.t -> string =
    function
    | NonTerm t ->  t
    | S         -> "S"

/// Point is a terminal or a non-terminal.
///
module rec Point =
  
  /// Point is a terminal or a non-terminal.
  ///
  type t =
    | T  of Term.t
    | NT of NonTerm.t

  let show : Point.t -> string =
    function
    | T  t -> Term.show t
    | NT t -> NonTerm.show t

module rec Rule =
  type t =
    { points : Point.t list
      mark   : string
    }

  let show (rule : Rule.t) : string =
    String.concat " " (List.map Point.show rule.points) + " {" + rule.mark + "}"

/// Grammar is an input for LR parser to generate all tables.
///
module rec Grammar =
  
  /// Grammar is a map from non-terminal names to disjoint union
  /// of their ways to build.
  ///
  type t = (NonTerm.t, Rule.t list) Map

  let show : Grammar.t -> string =
    fun grammar ->
      let ruleToString (name, rules) =
        String.concat "\n  | " <|
          (  (NonTerm.show name + " =")
          :: (rules |> List.map Rule.show)
          )
      
      grammar
        |> Map.toList
        |> Seq.map ruleToString
        |> String.concat "\n"

/// Custom extensions for Sets.
///
module Set =
  /// Return empty set if optional set is missing.
  ///
  let optional
    (opt : 'a Set option)
         : 'a Set
    = Option.defaultValue Set.empty opt

  /// Return `Some set` iff set isn't empty; return `None` otherwise.
  ///
  let nonEmpty
    : 'a Set -> 'a Set option
    = fun set ->
      if Set.isEmpty set
      then None
      else Some set
  
  /// Set difference.
  ///
  let minus part whole = Set.filter (fun v -> not <| Set.contains v whole) part

  /// Fill the set by spreading information accross it, by using the `step`
  /// function. Stop when `step` produces nothing new.
  ///
  let rec fixpoint
    (step  : 'a Set -> 'a Set)
    (start : 'a Set)
           : 'a Set
    = let next = Set.union (step start) start
      if next = start
      then start
      else fixpoint step next

  let show1 (show : 'a -> string) (set : 'a Set) : string =
    set
      |> Set.map show
      |> Set.toList
      |> String.concat " "
      |> (fun pts -> "{" + pts + "}")
  
/// Custom extensions for Maps.
///
module rec Map =
  /// Delete keys with empty values.
  ///
  let clean map
    = map
      |> Map.toList
      |> List.filter (fun (_, v) -> not <| Set.isEmpty v)
      |> Map.ofList

  /// Monoidal map difference
  ///
  let minus
    (part  : ('k, 'v Set) Map)
    (whole : ('k, 'v Set) Map)
           : ('k, 'v Set) Map
    = part
      |> Map.map (fun k v -> 
        match Map.tryFind k whole with
        | Some v1 -> Set.minus v1 v
        | None    -> v
      )
      |> clean

  /// Monoidal map union.
  ///
  let merge part whole = Map.foldBack (fun k v -> Map.change k (Set.optional >> Set.union v >> Set.nonEmpty)) part whole
  
  let lookup
    (map : ('k, 'v Set) Map)
    (key :  'k)
         :  'v Set
    = Map.tryFind key map |> Set.optional

  /// Fill the mapset by spreading information accross it, by using the `step`
  /// function. Stop when `step` produces nothing new.
  ///
  let rec fixpoint
    (step  : ('k, 'v Set) Map -> ('k, 'v Set) Map)
    (start : ('k, 'v Set) Map)
           : ('k, 'v Set) Map
    = let next = Map.merge (step start) start
      if next = start
      then start
      else fixpoint step next
    
let flip f x y = f y x

/// Table of terminals that can start a non-terminal.
///
module rec First =

  /// A map from non-terminal to a set of terminals that it can start with.
  ///
  type t = (NonTerm.t, Term.t Set) Map

  /// Build a FIRST map. Assumes that no rule accepts empty input.
  ///
  let from
    (grammar : Grammar.t)
             : First.t
    = let loop : First.t -> First.t = fun first ->
        grammar |> Map.map (fun s ptss ->       // for all rules in grammar
          let startOf (rule : Rule.t) =
            match List.head rule.points with
            | Point.T  s -> Set.ofList [s]      // the starting terminal is given
            | Point.NT s -> Map.lookup first s  // the starting terminals are as in other non-term 
          
          ptss
            |> List.map startOf
            |> Set.unionMany                    // join all possibilities
        )
      
      Map.ofList [NonTerm.S, Set.ofList []]
        |> Map.fixpoint loop                    // run until no new data generated

  let show
    : First.t -> string
    = Map.toList
    >> List.map (fun (s, terms) -> sprintf "%s = {%s}" (NonTerm.show s) (terms |> Set.toList |> List.map Term.show |> String.concat " "))
    >> String.concat "\n"

/// Table of terminals that can be seen right after a non-terminal.
///
module rec Follow =

  /// A map from non-terminal to a set of terminals that follow it.
  ///
  type t = (NonTerm.t, Term.t Set) Map

  let from
    (grammar : Grammar.t)
    (first   : First.t)
             : Follow.t
    = let loop
        (follow : Follow.t)
                : Follow.t
        = grammar
            |> Map.toList
            |> List.map (fun (super, rules) ->
              
              // Analyse each point and an optional following one.
              //
              let follows (pt, next) =
                match pt, next with
                | Point.NT nt, Some (Point.T term) -> Map.ofList [nt, Set.ofList [term]]
                | Point.NT nt, None                -> Map.ofList [nt, Map.lookup follow super]
                | Point.NT nt, Some (Point.NT nt1) -> Map.ofList [nt, Map.lookup first nt1]
                | _                                -> Map.empty

              // zipped [a; b; c] = [a, Some b; b, Some c; c, None]
              //
              let zipped (rule : Rule.t) = List.zip rule.points (List.map Some (List.tail rule.points) @ [None])

              rules
                |> List.map zipped              // analyse each rule variant
                |> List.map (List.map follows)  // collect all followings
                |> List.concat                  // merge
            )
            |> List.concat
            |> List.fold Map.merge Map.empty    // collect into one map
            |> Map.clean
      
      Map.ofList [NonTerm.S, Set.ofList [Term.Eof]]  // assume S can be followed by Eof
        |> Map.fixpoint loop

  let show
    : Follow.t -> string
    = First.show

/// Position inside an LR(1)-Item.
///
module rec Pos =

  /// Position is a zipper with optional locus.
  ///
  type t =
    { before : Point.t list
      locus  : Point.t option
      after  : Point.t list
    }

  /// Rules can't be nullary.
  ///
  exception RuleCannotBeNullary

  /// Turn rule into its initial position.
  ///
  let start (rule : Point.t list) : Pos.t =
    match rule with
    | [] -> raise RuleCannotBeNullary
    | pt :: rule ->
      { before = []
        locus  = Some pt
        after  = rule
      }

  /// Try navigating to the next position.
  ///
  let next (pos : Pos.t) : Pos.t option =
    pos.locus
      |> Option.map (fun pt -> 
        match pos.after with
        | next :: pts ->
          { before = pt :: pos.before
            locus  = Some next
            after  = pts
          }
        | [] ->
          { before = pt :: pos.before
            locus  = None
            after  = []
          }
      )

  let show (pos : Pos.t) : string
    = List.map Point.show (List.rev pos.before)
    @ [pos.locus |> Option.elim "[]" (fun l -> "[" + Point.show l + "]")]
    @ List.map Point.show pos.after
      |> String.concat " "
  
  let showOption (pos : Pos.t option) : string =
    pos |> Option.map show |> Option.defaultValue "-"

module rec Item =
  type t =
    { pos       : Pos.t
      lookahead : Term.t Set
      mark      : string
    }

  let show (item : Item.t) : string =
    Pos.show item.pos + " " + Set.show1 Term.show item.lookahead + " -> {" + item.mark + "}"
  
let t = Point.T << Term.Term << Lexeme.Concrete
let d = Point.T << Term.Term << Lexeme.Category
let n = Point.NT << NonTerm.NonTerm
let n1 = NonTerm.NonTerm
let s = Point.NT NonTerm.S
let r (m : string) (pt : Point.t list) : Rule.t =
  { points = pt
    mark   = m
  }

let map = Map.ofList
let set = Set.ofList

let arith
  : Grammar.t
  = Map.ofList
      [ NonTerm.S, [r "s" [n "E"]]
        n1 "E",    [r "plus" [n "E"; t "+"; n "T"]; r "t" [n "T"]]
        n1 "T",    [r "mult" [n "T"; t "*"; n "F"]; r "f" [n "F"]]
        n1 "F",    [r "num" [d "num"]; r "group" [t "("; n "E"; t ")"]]
      ]

let first
  : First.t
  = arith
    |> First.from

first
  |> First.show
  |> printfn "%s"

let follow
  : Follow.t
  = Follow.from arith first

follow
  |> Follow.show
  |> printfn "%s"

arith
  |> Grammar.show
  |> printfn "%s"
  
let rule = [n "E"; t "+"; n "T"]

printfn "%s" (Pos.start rule |> Pos.show)
printfn "%s" (Pos.start rule |> Pos.next |> Pos.showOption)
printfn "%s" (Pos.start rule |> Pos.next |> Option.bind Pos.next |> Pos.showOption)
printfn "%s" (Pos.start rule |> Pos.next |> Option.bind Pos.next |> Option.bind Pos.next |> Pos.showOption)
printfn "%s" (Pos.start rule |> Pos.next |> Option.bind Pos.next |> Option.bind Pos.next |> Option.bind Pos.next |> Pos.showOption)
