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
        TransactionType == {"buy", "cancel", "confirm", "deny", "reserve"} \* New type
        bankIDType == AllParticipants \union {-2}
        MessageType == [type : TransactionType,
                        from : IPs,
                        seat : Seats,
                        bankID : bankIDType]
        M0 == [type |-> "buy",
                 from |-> 0,
                 seat |-> 0,
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
    {
        s1: while (TRUE) {
            
            WW: 
            await (Len(Channels[ip]) > 0);
            
            GET:
            internalReq := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);
            
            TREAT:
            if (internalReq.type = "buy"){
                if (seatMap[internalReq.seat] = "reserved" /\ seatOwner[internalReq.seat] = internalReq.from /\ BankAccount[internalReq.bankID] > 0) { \* If it`s reserved
                    seatMap[internalReq.seat] := "paid";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                       ![0] = BankAccount[0] + 1];
                    \* seatOwner[internalReq.seat] := internalReq.from; 
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
                if (seatMap[internalReq.seat] = "paid" /\ seatOwner[internalReq.seat] = internalReq.from) { 
                    seatMap[internalReq.seat] := "available";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                       ![0] = BankAccount[0] - 1];

                    seatOwner[internalReq.seat] := 0;

                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "confirm", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> id]);
                } else if (seatMap[internalReq.seat] = "reserved" /\ seatOwner[internalReq.seat] = internalReq.from){ \*If it`s not paid yet
                seatOwner[internalReq.seat] := 0;
                seatMap[internalReq.seat] := "available";
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
            } else if (internalReq.type = "reserve") { \* New process
                if (seatMap[internalReq.seat] = "available") {
                    seatMap[internalReq.seat] := "reserved";
                    seatOwner[internalReq.seat] := internalReq.from; 
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
            seats_reserved = {}; \* add set to store reserved seats
            random_seat = 0; \* temp value to store random reserved seat to pay or cancel

    {
        ClientLoop: 
        while (state = "shopping") {

            CheckingTermination: 
            if (BankAccount[self] = 0 \/ Cardinality(tickets[self]) = ticketsWanted \/ rounds >= 2) {
                state := "done";
            }
            else {  
                if (current_seat > NUMSEATS) {
                    current_seat := 1;
                    rounds := rounds + 1;
                }
                else {
                    either{
                        await current_seat <= NUMSEATS;

                            TryReserve:
                            Channels[0] := Append(Channels[0],
                                [type |-> "reserve", from |-> self, seat |-> current_seat, bankID |-> self]);                        

                            WaitReserve:
                            await Len(Channels[self]) > 0;
                            ProcessReserve:
                            msg := Head(Channels[self]);
                            Channels[self] := Tail(Channels[self]);

                            if (msg.type = "confirm") { 
                                seats_reserved := seats_reserved \union {msg.seat}; \* append the seat to the list
                            };
                            current_seat := current_seat + 1;
                        
                    }
                    or {
                        await seats_reserved /= {};
                        TryBuy:
                        random_seat := CHOOSE r \in seats_reserved : TRUE; \* to avoid using with (random_seat \in seats_reserved)
                            
                        Channels[0] := Append(Channels[0],
                            [type |-> "buy", from |-> self, seat |-> random_seat, bankID |-> self]);
            
                        WaitBuy:
                        await Len(Channels[self]) > 0;
            
                        ProcessBuy:
                        msg := Head(Channels[self]);
                        Channels[self] := Tail(Channels[self]);
            
                        if (msg.type = "confirm") {
                            tickets[self] := tickets[self] \union {msg.seat};
                            seats_reserved := seats_reserved \ {random_seat};
                        };
                        DemandCancelReserve:
                        if (msg.type = "deny") {
                            Channels[0] := Append(Channels[0], \* Cancel reserved if fails
                                [type |-> "cancel", from |-> self, seat |->  random_seat, bankID |-> self]);
                        };
                        CancelReserve:
                        if (msg.type = "deny") {                      
                            await Len(Channels[self]) > 0; \* Wait for cancel message
                            msg := Head(Channels[self]); \* Process cancel
                             Channels[self] := Tail(Channels[self]);

                            if(msg.type = "confirm") {
                                seats_reserved := seats_reserved \ {random_seat};
                            }
                        };
                        
                    }
                    or { 
                        await tickets[self] /= {};  

                        TryCancel:
                        if (tickets[self] /= {}) { 
                            with (last_ticket = CHOOSE t \in tickets[self] : \A other \in tickets[self] : t >= other) {
                                Channels[0] := Append(Channels[0],
                                    [type |-> "cancel", from |-> self, seat |->  last_ticket, bankID |-> self]);
                                };

                                WaitCancel:
                                await Len(Channels[self]) > 0;

                                ProcessCancel:
                                msg := Head(Channels[self]);
                                Channels[self] := Tail(Channels[self]);

                                if(msg.type = "confirm") {
                                    tickets[self] := tickets[self] \ {msg.seat};
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
                [type |-> "cancel", from |-> self, seat |->  current_seat_m, bankID |-> self]);

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









