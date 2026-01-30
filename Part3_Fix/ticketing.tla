----------------------------- MODULE ticketing -----------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x \in AllHonest THEN INITMONEY ELSE 0]; \* if its honest it starts with money, but the rest (server or malicius) starts with 0
        Channels = [x \in AllParticipants |-> <<>>];  \* Channels[ip] is the queue for messages TO ip. Starts empty.
        tickets = [x \in 1..NUMCLIENTS |-> {}];  \* All tickets starts empty
        seatMap = [s \in 1..NUMSEATS |-> "available"]; \* All seats start as available 
        \* it's a global variable to be used in the Invariant TypeOk
        
        seatOwner = [s \in 1..NUMSEATS |-> 0]; \* Part 3 new variable to keep track of who bought the seat.
        \* All seats starts belonging to the server


    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0} \* 0 is the server
        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid"}
        seatMapType == [Seats -> SeatStates]
        IPs == Nat \* IP addresses are natural numbers
        TransactionType == {"buy", "cancel", "confirm", "deny"}
        bankIDType == AllParticipants \union {-2} \* -2 is for "not given"
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
            /\ \A x \in AllParticipants : BankAccount[x] >= -1 \* putting here -1 just to be safe with malicius
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

    fair process (Server = 0) \* Server has process ID 0
    variables
        id = 0; \* Server's BankID
        ip = 0; \* Server's IP address
        internalReq = M0; \* Dummy var 
    {
        s1: while (TRUE) {
            \* Wait for a message to process
            WW: 
            await (Len(Channels[ip]) > 0);
            \* Read the first inline
            GET:
            internalReq := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);
            
            TREAT:
            if (internalReq.type = "buy"){
                if (seatMap[internalReq.seat] = "available" 
                    /\ BankAccount[internalReq.bankID] > 0) {
                    seatMap[internalReq.seat] := "paid";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                       ![0] = BankAccount[0] + 1];

                    seatOwner[internalReq.seat] := internalReq.from; 
                    \* Part3 add: When HClient buys the seat, it gets assigned to his ID

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
                                                        \* Part3 add: Checks if the seat owner ID is the same as the request
                    
                    seatMap[internalReq.seat] := "available";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                       ![0] = BankAccount[0] - 1];

                    seatOwner[internalReq.seat] = 0;
                    \* Part3 add: Seat ownership goes back to the server

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
            }
            \* Ignore other message types
        }
    }

    fair process (HClient \in AllHonest) 
        variables 
            id = self; \* Client's BankID
            ip = self; \* Client's IP address
            state = "shopping"; \* Client's state
            msg = M0; \* temporary variable to hold received messages
            ticketsWanted \in 1..NUMSEATS; 
            current_seat = 1;  \* The seat that he wants to buy at the moment

            \* the client starts at round 0, if he pass by all seats and dont find any, he can do
            \* it one more time to see if anyone cancelled a ticket and he has a new opportunity to buy a ticket
            rounds = 0; 

    {
        ClientLoop: 
        while (state = "shopping") {

            \* If he has no money, or if he's already satisfied with the tickets, or there's no more avaiable seats to buy (after 2 rounds), the system stops.
            CheckingTermination: 
            if (BankAccount[self] = 0 \/ Cardinality(tickets[self]) = ticketsWanted \/ rounds >= 2) {
                state := "done";
            }
            else {  \* here is the logic of the rounds, if he pass by the last seat he adds one round and try again from seat 1
                if (current_seat > NUMSEATS) {
                    current_seat := 1;
                    rounds := rounds + 1;
                }
                else {
                    either{
                        \* He will try to buy the current seat
                        if (current_seat <= NUMSEATS) {  \* only if has seats available
                            TryBuy:
                            Channels[0] := Append(Channels[0],
                                [type |-> "buy", from |-> self, seat |-> current_seat, bankID |-> self]);
            
                            \* He waits for a answer
                            WaitBuy:
                            await Len(Channels[self]) > 0;
            
                            \* He process the answer
                            ProcessBuy:
                            msg := Head(Channels[self]);
                            Channels[self] := Tail(Channels[self]);
            
                            if (msg.type = "confirm") {
                                tickets[self] := tickets[self] \union {msg.seat};
                            };
                            \* Doing a Sequencial Strategy here, to ensures that it never gets stuck in a loop
                            \* Regardless of whether it succeeded or it was occupied, he advances to the next seat
                            current_seat := current_seat + 1;
                        }
                    }
                    or { 
                        await tickets[self] /= {};  
                        \* New line because in one time line a client was trying to infinite refund a ticket he doesn't have

                        \* He try to cancel a ticket but only if he already has any ticket
                        TryCancel:
                        if (tickets[self] /= {}) { 
                            \* I reduced the complexity here by allowing him to cancel only the last ticket purchased 
                            with (last_ticket = CHOOSE t \in tickets[self] : \A other \in tickets[self] : t >= other) {
                                \* "SendCancel:"
                                Channels[0] := Append(Channels[0],
                                    [type |-> "cancel", from |-> self, seat |->  last_ticket, bankID |-> self]);
                                };
                                \* He waits for a answer
                                WaitCancel:
                                await Len(Channels[self]) > 0;

                                \* He process the answer
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
            current_seat_m = 1; \* "1" will be changed, just a placeholder
            msg_m = M0;

    {
        MaliciousLoop:
        while (TRUE) {
            WaitForHonestClient: \* To avoid trying selected a paid seat that do not exist
            await \E seat \in 1..NUMSEATS: seatMap[seat] = "paid";
            
            TargetPaidSeat:
            with (seat \in {seat \in 1..NUMSEATS : seatMap[seat] = "paid"}) {
                current_seat_m := seat;
            };

            RunScam: \* He sends the same cancel message as an Honest Client, but with his bank ID
            Channels[0] := Append(Channels[0],
                [type |-> "cancel", from |-> self, seat |->  current_seat_m, bankID |-> self]);

            WaitCancel: \* Malicious Client was spamming cancel messages before the server answer
            await Len(Channels[self]) > 0;
            ProcessCancel: \* Same logic as Honest client
            msg_m := Head(Channels[self]);
            Channels[self] := Tail(Channels[self]);
            }
        }
    }
*)
\* END TRANSLATION 


=============================================================================



