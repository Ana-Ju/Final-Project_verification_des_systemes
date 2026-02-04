----------------------------- MODULE ticketing -----------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x \in AllHonest THEN INITMONEY ELSE 0];
        Channels = [x \in AllParticipants |-> <<>>]; 
        tickets = [x \in 1..NUMCLIENTS |-> {}]; 
        seatMap = [s \in 1..NUMSEATS |-> "available"];
        
        
        seatOwner = [s \in 1..NUMSEATS |-> 0];
        


    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}
        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid", "reserved"} \* New state
        seatMapType == [Seats -> SeatStates]
        IPs == Nat \* IP addresses are natural numbers
        TransactionType == {"buy", "cancel", "confirm", "deny", "reserve", "query", "info"} \* New type
        bankIDType == AllParticipants \union {-2}
        MessageType == [type : TransactionType,
                        from : IPs,
                        seat : SUBSET Seats,
                        bankID : bankIDType]
        M0 == [type |-> "buy",
                 from |-> 0,
                 seat |-> {},
                 bankID |-> 0]


        \* -------- Invariants --------

        \*Type: This will ensure that the variables always hold the correct type of data
        TypeOK ==
            /\ \A x \in AllParticipants : BankAccount[x] >= -1
            /\ \A s \in Seats : seatMap[s] \in SeatStates
            /\ \A c \in AllHonest : tickets[c] \subseteq Seats
            /\ \A x \in AllParticipants : IsFiniteSet(Channels[x])

        \* Conservation of Money: The money the  client has in their pocket + the value of the tickets (price = 1)
        \* must be equal to the amount of money they had at the beginning
        MoneyConservation ==   
            \A c \in AllHonest : BankAccount[c] + Cardinality(tickets[c]) = INITMONEY

        \* -------- Temporal Properties --------

        \* Liveness: The system must eventually stop
        AllClientsFinish ==
            <>(\A c \in AllHonest : pc[c] = "Done")

    }

    fair process (Server = 0)
    variables
        id = 0; 
        ip = 0;
        internalReq = M0;
        cost = 0;
        availableSet = {} \* to calculate the query response

    {
        s1: while (TRUE) {
            
            WW: 
            await (Len(Channels[ip]) > 0);
            
            GET:
            internalReq := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);

            cost := Cardinality(internalReq.seat); \* The cost is based on the number of seats in the set
            
            TREAT:
            if (internalReq.type = "buy"){
                \* Check if all seats in the set can be purchased. They can be purchased if available or if reserved and the owner is the one requesting them
                if ((\A s \in internalReq.seat : seatMap[s] = "available" \/ (seatMap[s] = "reserved" /\ seatOwner[s] = internalReq.from))
                    /\ BankAccount[internalReq.bankID] >= cost) { 

                    seatMap := [s \in Seats |-> IF s \in internalReq.seat THEN "paid" ELSE seatMap [s]];  \*Update the map
                    seatOwner := [s \in Seats |-> IF s \in internalReq.seat THEN  internalReq.from ELSE seatOwner[s]];  \* Defines the ultimate owner

                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - cost,
                                                       ![0] = BankAccount[0] + cost];
                     
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                [type |-> "confirm", 
                                                 from |-> 0, 
                                                 seat |-> internalReq.seat, 
                                                 bankID |-> -2]);
                }
                else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                [type |-> "deny", 
                                                 from |-> 0, 
                                                 seat |-> internalReq.seat, 
                                                 bankID |-> -2]);
                }
            } else if (internalReq.type = "cancel") {
                \* Check if all seats belong to the client
                if (\A s \in internalReq.seat : (seatMap[s] = "paid" \/ seatMap[s] = "reserved") /\ seatOwner[s] = internalReq.from) { 
                    seatMap := [s \in Seats |-> IF s \in internalReq.seat THEN "available" ELSE seatMap[s]]; \* Free up all seats in the set
                    seatOwner := [s \in Seats |-> IF s \in internalReq.seat THEN 0 ELSE seatOwner[s]];

                    \* Return the money only if it has already been paid
                    if (\A s \in internalReq.seat : seatMap[s] = "paid") {
                        BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + cost,
                                                           ![0] = BankAccount[0] - cost];
                    };

                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "confirm", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> id]);
                } else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "deny", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> id]);
                }

            } else if (internalReq.type = "reserve") { 
                if (\A s \in internalReq.seat : seatMap[s] = "available") {
                    seatMap := [s \in Seats |-> IF s \in internalReq.seat THEN "reserved" ELSE seatMap[s]];
                    seatOwner := [s \in Seats |-> IF s \in internalReq.seat THEN internalReq.from ELSE seatOwner[s]];
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                [type |-> "confirm", 
                                                 from |-> 0, 
                                                 seat |-> internalReq.seat, 
                                                 bankID |-> id]);
                 } else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                [type |-> "deny", 
                                                 from |-> 0, 
                                                 seat |-> internalReq.seat, 
                                                 bankID |-> -2]);
                }
            } else if (internalReq.type = "query") {
                availableSet := {s \in Seats : seatMap[s] = "available"};
                Channels[internalReq.from] := Append(Channels[internalReq.from],
                    [type |-> "info", from |-> 0, seat |-> availableSet, bankID |-> -2]);

            }
        }
    }

    fair process (HClient \in AllHonest) 
        variables 
            id = self;
            ip = self;
            state = "shopping";
            msg = M0;
            ticketsWanted \in 1..NUMSEATS; 
            current_seat = 1;
            rounds = 0;
            my_batch = {}; \* Variable for assembling the purchase lot
            known_available = {}; \* Seats that the customer knows are available

    {
        ClientLoop: 
        while (state = "shopping") {

            CheckingTermination: 
            if (BankAccount[self] = 0 \/ Cardinality(tickets[self]) = ticketsWanted \/ rounds >= 2) {
                state := "done";
            }
            else {
                if (known_available = {}) {
                    SendQuery:
                    Channels[0] := Append(Channels[0], type |-> "query", from |-> self, seat|-> {}, bankID |-> self]);

                    WaitInfo:
                    await Len(Channels[self]) > 0;
                    msg := Head(Channels[self]);
                    Channels[self] := Tail(Channels[self]);

                    if (msg.type = "info") {
                        know_available := msg.seat;
                        \* it counts as a round if the server says there is nothing available to buy (failed attempt)
                        if (known_available = {}) {
                            rounds := rounds +1;
                        };
                    };
                }
                else { \* Choose the first N available seats from the list to purchase
                    my_batch := { x \in known_available :
                                  Cardinality({ y \in known_available : y <= x}) <= (ticketsWanted - Cardinality(tickets[self])) 
                                }; \* it only retrieves the N smallest available IDs

                    either{    
                            TryReserveBatch: 
                            Channels[0] := Append(Channels[0],
                                [type |-> "reserve", from |-> self, seat |-> my_batch, bankID |-> self]);                        
    
                            WaitReserve:
                            await Len(Channels[self]) > 0;
                            ProcessReserve:
                            msg := Head(Channels[self]);
                            Channels[self] := Tail(Channels[self]);
    
                            if (msg.type = "confirm") { 
                                    SendBuyBatch:
                                    Channels[0] := Append(Channels[0],
                                        [type |-> "buy", from |-> self, seat |-> my_batch, bankID |-> self]);

                                    WaitBuy:
                                    await Len(Channels[self]) > 0;
                        
                                    ProcessBuy:
                                    msg := Head(Channels[self]);
                                    Channels[self] := Tail(Channels[self]);
                        
                                    if (msg.type = "confirm") {
                                        tickets[self] := tickets[self] \union msg.seat;
                                        know_available := {};
                                    } else { 
                                        SendCancelReserve:
                                        Channels[0] := Append(Channels[0], \* Cancel reserved if payment fails 
                                            [type |-> "cancel", from |-> self, seat |->  my_batch, bankID |-> self]);

                                        WaitCancelCleanup: await Len(Channels[self]) > 0;
                                        Channels[self] := Tail(Channels[self]);
                                        know_available := {};
                                    }
                                } else { \* the reservation failed
                                    know_available := {};
                                };                            
                    }
                    or {
                        TryCancel:
                        if (tickets[self] /= {}) { 
                            Channels[0] := Append(Channels[0],
                                [type |-> "cancel", from |-> self, seat |->  tickets[self], bankID |-> self]);
                                    
                            WaitCancel:
                            await Len(Channels[self]) > 0;
    
                            ProcessCancel:
                            msg := Head(Channels[self]);
                            Channels[self] := Tail(Channels[self]);
    
                            if(msg.type = "confirm") {
                                tickets[self] := tickets[self] \ msg.seat;
                                know_available := {};
                                
                            }
                        }
                    }
                }
            } 
        }
    }
    fair process (MClient \in AllMalicious)
        variables
            id_m = self;
            current_seat_m = 1; 
            msg_m = M0;
            rounds = 0; 
            money_start = 0; 

    {
        MaliciousLoop:
        while (rounds < 2) {
            ActualMoney: 
            money_start := BankAccount[self];

            WaitForHonestClient: 
            await \E seat \in 1..NUMSEATS: seatMap[seat] = "paid";
            
            TargetPaidSeat:
            with (seat \in {seat \in 1..NUMSEATS : seatMap[seat] = "paid"}) {
                current_seat_m := seat;
            };

            RunScam: 
            Channels[0] := Append(Channels[0],
                [type |-> "cancel", from |-> self, seat |->  {current_seat_m}, bankID |-> self]);

            WaitCancel: 
            await Len(Channels[self]) > 0;
            ProcessCancel: 
            msg_m := Head(Channels[self]);
            Channels[self] := Tail(Channels[self]);

            VerifyScamFail:
            if (BankAccount[self] = money_start) {
                rounds := rounds + 1; }
            }
        }
    }
*)
\* END TRANSLATION 


=============================================================================













