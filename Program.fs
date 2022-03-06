open System
open System
open System
open System
open System
open System


#nowarn "62"
#nowarn "40"

module List =
  let rec drop n list =
    match n, list with
    | 0, list    -> list
    | _, []      -> list
    | n, _ :: xs -> drop (n - 1) xs

  let rec splitAt n list =
    match n, list with
    | 0, list -> ([], list)
    | n, x :: xs ->
      let (l, r) = splitAt (n - 1) xs
      (x :: l, r)

module Option =
  exception EmptyOption

  let elim
    (none : 'c)
    (some : 'a -> 'c)
    (opt  : 'a option)
          : 'c
    = opt
      |> Option.map some
      |> Option.defaultValue none

  let unsafeUnwrap
    (opt : 'a option)
         : 'a
    = Option.defaultWith (fun () -> raise EmptyOption) opt

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
    | Concrete t -> t
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
    { entity : NonTerm.t
      points : Point.t list
      mark   : string
    }

  let show (rule : Rule.t) : string =
    rule.mark + ".\t" + NonTerm.show rule.entity + " = " + String.concat " " (List.map Point.show rule.points)

/// Grammar is an input for LR parser to generate all tables.
///
module rec Grammar =
  
  /// Grammar is a map from non-terminal names to disjoint union
  /// of their ways to build.
  ///
  type t = (NonTerm.t, Rule.t list) Map

  let show : Grammar.t -> string =
    fun grammar ->
      grammar
        |> Map.values
        |> Seq.map (List.map Rule.show)
        |> List.concat
        |> String.concat "\n"

  let addInternal
    (entity  : NonTerm.t)
    (mark    : string)
    (points  : Point.t list)
             : Grammar.t -> Grammar.t
    =
      Map.change entity
        <| fun cases ->
          Some
            <| { entity = entity
                 points = points
                 mark   = mark
               } :: Option.defaultValue [] cases

  let addS : string -> Point.t list -> Grammar.t -> Grammar.t
    = addInternal NonTerm.S 

  let add (entity : string) : string -> Point.t list -> Grammar.t -> Grammar.t
    = addInternal <| NonTerm.NonTerm entity
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

  let bind (f : 'a -> 'b Set) (set : 'a Set) : 'b Set =
    Set.map f set |> Set.unionMany

  let show1 (show : 'a -> string) (set : 'a Set) : string =
    set
      |> Set.map show
      |> Set.toList
      |> String.concat " "
      //|> (fun pts -> "{" + pts + "}")
  
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

  let mergeWith
    (f : 'a -> 'a -> 'a)
    (left  : ('k, 'a) Map)
    (right : ('k, 'a) Map)
           : ('k, 'a) Map
    =
      Map.foldBack (fun k v -> Map.change k (Option.elim v (f v) >> Some)) left right

  let union (left : ('k, 'a) Map) (right : ('k, 'a) Map) : ('k, 'a) Map =
    Map.mergeWith (fun x y -> y) left right

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
    >> List.map (fun (s, terms) -> sprintf "%s = %s" (NonTerm.show s) (Set.show1 Term.show terms))
    >> String.concat "\n"

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

  let length (pos : Pos.t) = List.length pos.before + List.length pos.after + Option.elim 0 (fun _ -> 1) pos.locus

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

/// Position of parser in relation to one rule.
///
module rec Item =

  /// Carries name, points and mark from the rule.
  /// Also contains lookahead.
  ///
  type t =
    { entity    : NonTerm.t
      pos       : Pos.t
      lookahead : Term.t Set
      mark      : string
    }

  /// Create item from rule in the starting postion.
  ///
  let start (lookahead : Term.t Set) (rule : Rule.t) : Item.t =
    { Item.entity    = rule.entity
      Item.pos       = Pos.start rule.points
      Item.lookahead = lookahead
      Item.mark      = rule.mark
    }

  let length (item : Item.t) = Pos.length item.pos

  /// Move to the next point of the originating rule.
  ///
  let next (item : Item.t) : Item.t option =
    Pos.next item.pos
      |> Option.map (fun newPos -> { item with pos = newPos })

  /// Get current point, if it has one.
  ///
  let locus (item : Item.t) : Point.t option =
    item.pos.locus

  let show (item : Item.t) : string =
    item.mark + ".\t" + NonTerm.show item.entity + " = " + Pos.show item.pos + " --- " + Set.show1 Term.show item.lookahead
  
exception RuleIsNotDefined of NonTerm.t

/// Parser state.
///
module rec State =

  /// Contains all the positions the parser is in now.
  ///
  /// For instance, if parser is in
  ///   F = [A] b --- d e
  /// and
  ///   A = c
  /// then the state of the parser will be
  ///   F = [A] b --- d e;
  ///   A = [c]   --- b   
  ///
  /// That is because [A] is an entity of length > 1, we will go into on any FIRST(A).
  ///
  type t = Item.t Set

  type index = int

  /// Type to collect all states into.
  ///
  type reg =
    { indices : (State.t, State.index) Map
      states  : (State.index, State.t) Map
      counter : State.index
    }

  let emptyReg : reg =
    { indices = Map.empty
      states  = Map.empty
      counter = 0
    }

  let add (state : State.t) (reg : State.reg) : State.index * State.reg * bool =
    match reg.indices |> Map.tryFind state with
    | Some existing -> existing, reg, true
    | None ->
      reg.counter,  
        { reg with
            indices = Map.add state reg.counter reg.indices
            states  = Map.add reg.counter state reg.states
            counter = reg.counter + 1
        }, false

  /// Group items from state that differ only in lookaheads,
  /// and join the groups into single items with combined lookaheads.
  ///
  let normalize (state : State.t) : State.t =
    state
      |> Set.toList
      |> List.groupBy (fun item -> item.pos)
      |> List.map (fun (_, items) ->
          { List.head items with
              lookahead =
                items
                  |> List.map (fun item -> item.lookahead)
                  |> Set.unionMany
          }
       )
      |> Set.ofList

  /// Calculate CLOSURE of an item with given lookahead, using grammar and FIRST.
  ///
  let closureOf
    (grammar   : Grammar.t)
    (first     : First.t)
    (item      : Item.t)
               : State.t
    =
      let loop (state : State.t) : State.t =
        state
          |> Set.bind (fun item ->
            match item.pos.locus with
            | None             -> Set.empty                            // Finished items produce nothing.
            | Some (Point.T _) -> Set.empty                            // Same for token-next ones.
            | Some (Point.NT nonTerm) ->                               // Non-terminals produce initial states
              match Map.tryFind nonTerm grammar with                   //  of their rules.
              | None -> raise <| RuleIsNotDefined nonTerm
              | Some rules ->
                let localahead =                                       // To find the new lookahead, 
                  match Item.next item |> Option.bind Item.locus with  // we check next locus of item:
                  | None                 -> item.lookahead             //  if it's empty, we use current item's lookahead;
                  | Some (Point.T  term) -> Set.ofList [term]          //  if it's term, we use it;
                  | Some (Point.NT nt)   -> Map.lookup first nt        //  if it's non-term, we use its FIRST set,
                
                rules
                  |> List.map (Item.start localahead)
                  |> Set.ofList
          )

      Set.ofList [item]
        |> Set.fixpoint loop
        |> normalize

  let firstState (grammar : Grammar.t) (first : First.t) : State.t =
    Map.find NonTerm.S grammar
      |> List.map (Item.start <| Set.ofList [Term.Eof])
      |> Set.ofList
      |> Set.bind (closureOf grammar first)


  let show (state : State.t) : string =
    state
      |> Set.map Item.show
      |> Set.toList
      |> String.concat "\n"

  let showReg (reg : State.reg) : string =
    reg.states
      |> Map.toList
      |> List.map (fun (ix, state) -> "-- " + ix.ToString() + " --\n" + State.show state + "\n")
      |> String.concat "\n"

open State

module rec Goto =
  type t = (State.index, (NonTerm.t, State.index) Map) Map

  let from
    (grammar : Grammar.t)
    (first   : First.t)
             : Goto.t * State.reg
    =
      let closure = State.closureOf grammar first
      
      // Loop, while keeping a pool of new discovered states until no new state is found.
      //
      let rec loop
        ( goto   : Goto.t
        , reg    : State.reg
        , states : State.index Set
        )        : Goto.t * State.reg
        =
        
          // Registed all moves fron the state and find new reachable states.
          //
          let moves
            ( goto  : Goto.t
            , reg   : State.reg
            , next  : State.index Set
            )
            ( state : State.index)
                    : Goto.t * State.reg * State.index Set
            =
              let itemset = reg.states.Item state
          
              // Get all State, Point, NextState to put into GOTO table.
              //
              let endRules =
                itemset
                  |> Set.map  (fun item -> Item.locus item, Item.next item)
                  |> Set.bind (fun (locus, next) ->
                    match locus, next with
                    | Some locus, Some next -> Set.ofList [state, locus, closure next]
                    | _                     -> Set.empty
                  )

              // Registes NextState from (State, Point, NextState), add it to GOTO.
              //
              // If the state is new, add it to the `next` set.
              //
              let addState
                ( goto   : Goto.t
                , reg    : State.reg
                , next   : State.index Set
                )
                ( source : State.index
                , point  : Point.t
                , dest   : State.t
                )        : Goto.t * State.reg * State.index Set
                =
                let ix, reg, existed = State.add dest reg             // register destination state
                let goto = 
                  match point with
                  | Point.T t -> goto
                  | Point.NT nt ->
                      Map.mergeWith Map.union (Map.ofList [source, Map.ofList [nt, ix]]) goto            // add transition
                let next = if existed then next else Set.add ix next  // if destination is new, add it to the pool
                goto, reg, next

              endRules
                |> Set.fold addState (goto, reg, next)              // for each transition from state

          let (goto, reg, next) =
            states
              |> Set.fold moves (goto, reg, Set.empty)            // for each state in the pool

          if Set.isEmpty next
          then goto, reg
          else loop (goto, reg, next)

      let state0 = State.firstState grammar first
      let ix, reg, _ = State.emptyReg |> State.add state0

      loop (Map.empty, reg, Set.ofList [ix])

  let show (goto : Goto.t) : string =
    goto
      |> Map.toList
      |> List.map (fun (src, ptDestMap) ->
          src.ToString() + ":\n" + String.concat "\n" ((List.map (fun (pt, dest) -> "  " + NonTerm.show pt + " -> " + dest.ToString()) <| Map.toList ptDestMap))
      )
      |> String.concat "\n"

module rec Action =
  type act =
    | Shift of State.index
    | Reduce of int * string * NonTerm.t
    | Accept
    | Conflict of act list
  
  type t = (State.index, (Term.t, act) Map) Map

  let mergeAct (left : act) (right : act) : act =
    match left, right with
    | Conflict az, Conflict bz -> Conflict ( az    @  bz)
    | Conflict az, right       -> Conflict ( az    @ [right])
    | left,        Conflict bz -> Conflict ([left] @  bz)
    | left,        right       -> Conflict ([left;    right])

  let merge : Action.t -> Action.t -> Action.t =
    mergeAct
      |> Map.mergeWith
      |> Map.mergeWith

  let from
    (grammar : Grammar.t)
    (first   : First.t)
    (reg     : State.reg)
    (start   : State.index)
             : Action.t
    =
      let closure = State.closureOf grammar first

      let states =
        Map.keys reg.states
          |> Seq.toList
     
      // Add actions on given state.
      //
      let action (ix : State.index) : Action.t =
        let state = reg.states.Item ix                          
        state
          |> Set.toList
          |> List.map (fun item ->                              // for each item in state
            match Item.locus item with                            // match locus
            | Some (Point.NT nt)   -> Map.empty                     // non-term? ignore
            | Some (Point.T  term) ->                               // term?
              let next = Item.next item |> Option.unsafeUnwrap        // get next item after term
              let state = closure next                                // make item into state
              let index = reg.indices.Item state                      // find that state in state registry
              Map.ofList [ix, Map.ofList [term, Shift index]]         // produce `Shift` action
            | None ->                                               // end-of-rule?
              if item.entity = NonTerm.S                              // start action?
              then
                Map.ofList [ix, Map.ofList [Term.Eof, Accept]]          // produce `Accept`
              else
                item.lookahead
                  |> Set.toList
                  |> List.map (fun term ->                            // add `Reduce` action
                      Map.ofList [ix, Map.ofList [term, Reduce (Item.length item, item.mark, item.entity)]]
                    )
                  |> List.fold merge Map.empty
          )
          |> List.fold merge Map.empty

      states
        |> List.map action
        |> List.fold merge Map.empty

  let rec showAct : act -> string =
    function
    | Shift   state          -> "Shift "  + state.ToString()
    | Reduce (size, mark, e) -> "Reduce " + mark + "/" + size.ToString() + " -> " + NonTerm.show e
    | Accept                 -> "Accept"
    | Conflict acts          -> "Conflict [" + String.concat ", " (List.map showAct acts) + "]"

  let show (goto : Action.t) : string =
    goto
      |> Map.toList
      |> List.map (fun (src, ptDestMap) ->
          src.ToString() + ":\n" + String.concat "\n" ((List.map (fun (pt, dest) -> "  " + Term.show pt + " -> " + showAct dest) <| Map.toList ptDestMap))
      )
      |> String.concat "\n"

module Parser =

  exception Expected of Term.t seq * Term.t

  type 'a tree =
    | Leaf of 'a
    | Node of string * 'a tree list

  let run
    (action : Action.t)
    (goto   : Goto.t)
    (state  : State.index)
    (input  : (Term.t * 'a) list)
            : State.index list * 'a tree list
    =
      let rec consume (top :: states, values) (token, str) =
        printfn "%A <- %A" (top :: states, values) (token, str)
        printfn "%s" <| Action.show (Map.ofList [top, action.Item(top)])
        printfn ""
        match action.Item(top).TryFind(token) with
        | Some (Action.Shift toState)         -> (toState :: top :: states, Leaf str :: values)
        | Some  Action.Accept                 -> (top :: states, [Node ("s", values)])
        | Some (Action.Reduce (len, mark, e)) ->
          let top :: states = List.drop len (top :: states)
          let (taken, rest) = List.splitAt len values
          consume (goto.Item(top).Item(e) :: top :: states, Node (mark, taken) :: rest) (token, str)
        | None ->
          raise <| Expected (Map.keys <| action.Item(top), token)
      List.fold consume ([state], []) input

let t = Point.T << Term.Term << Lexeme.Concrete
let d = Point.T << Term.Term << Lexeme.Category
let n = Point.NT << NonTerm.NonTerm
let n1 = NonTerm.NonTerm
let s = Point.NT NonTerm.S


let map = Map.ofList
let set = Set.ofList

let arith
  : Grammar.t
  = Map.empty
    |> Grammar.addS     "s"    [n "E"]

    |> Grammar.add  "E" "plus" [n "E"; t "+"; n "T"]
    |> Grammar.add  "E" "t"    [n "T"]

    |> Grammar.add  "T" "mult" [n "T"; t "*"; n "F"]
    |> Grammar.add  "T" "f"    [n "F"]
    
    |> Grammar.add  "F" "fnum" [d "num"]
    |> Grammar.add  "F" "grp"  [t "("; n "E"; t ")"]

arith
  |> Grammar.show
  |> printfn "GRAMMAR\n%s\n"
  
let first
  : First.t
  = arith
    |> First.from

first
  |> First.show
  |> printfn "FIRST\n%s\n"

let rule = [n "E"; t "+"; n "T"]

let closure = State.closureOf arith first

{ Rule.entity = NonTerm.NonTerm "F"
  Rule.mark   = "grp"
  Rule.points = [t "("; n "E"; t ")"]
}
  |> Item.start (Set.ofList [Term.Term <| Lexeme.Concrete "*"])
  |> Item.next
  |> Option.unsafeUnwrap
  |> closure
  |> State.show
  |> printfn "%s\n"

let goto, reg = Goto.from arith first
printfn "STATES"
printfn "%s" (State.showReg reg)
printfn "GOTO"
printfn "%s\n" (Goto.show goto)

let action = Action.from arith first reg 0

action
  |> Action.show
  |> printfn "%s"

exception Die

try
  Parser.run action goto 0
    [ Term.Term (Lexeme.Concrete "("), "("
      Term.Term (Lexeme.Category "num"), "1"
      Term.Term (Lexeme.Concrete ")"), ")"
    ]
    |> printfn "%A"
with Parser.Expected (terms, got) ->
  printfn "Expected %A, got %A" terms got
  raise Die