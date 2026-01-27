----------------------------- MODULE ticketing -----------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets, helpers

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x \in AllHonest THEN INITMONEY ELSE 0]; \* if its honest it starts with money, but the rest (server or malicius) starts with 0
        Channels = [x \in AllParticipants |-> <<>>];  \* Channels[ip] is the queue for messages TO ip. Starts empty.
      



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
        \* Create your invariants here

        \* Conservation of Money: The money the  client has in their pocket + the value of the tickets (price = 1)
        \* must be equal to the amount of money they had at the beginning
        MoneyConservation ==   
            \A c \in AllHonest : BanckAccount[c] + Cardinality(tickets[c]) = INITMONEY

        \* -------- Temporal Properties --------
        \* Create meaningful temporal properties if possible

        \* Liveness: The system must eventually stop
        AllClientsFinish ==
            <>(\A c \in AllHonest : pc[c] = "Done")

    }

    fair process (Server = 0) \* Server has process ID 0
    variables
        seatMap = [s \in Seats |-> "available"]; \* All seats start as available
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
                if (seatMap[internalReq.seat] = "paid") {
                    seatMap[internalReq.seat] := "available";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                       ![0] = BankAccount[0] - 1];
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
            tickets = {};
            id = self; \* Client's BankID
            ip = self; \* Client's IP address
            state = "shopping"; \* Client's state
            msg = M0 \* temporary variable to hold received messages
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
            if (BankAccount[self] = 0 \/ Cardinality(tickets) = ticketsWanted \/ rounds >= 2) {
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
                                tickets := tickets \union {msg.seat};
                            };
                            \* Doing a Sequencial Strategy here, to ensures that it never gets stuck in a loop
                            \* Regardless of whether it succeeded or it was occupied, he advances to the next seat
                            current_seat := current_seat + 1;
                        }
                    }
                    or { 
                        \* He try to cancel a ticket but only if he already has any ticket
                        TryCancel:
                        if (tickets /= {}) { 
                            \* I reduced the complexity here by allowing him to cancel only the last ticket purchased 
                            let (last_ticket == CHOOSE t \in tickets : \A other \in tickets : t >= other) {
                                SendCancel:
                                Channels[0] := Append(Channels[0],
                                    [type |-> "cancel", from |-> self, seat |->  last_ticket, bankID |-> self]);
                               
                                \* He waits for a answer
                                WaitCancel:
                                await Len(Channels[self]) > 0;

                                \* He process the answer
                                ProcessCancel:
                                msg := Head(Channels[self]);
                                Channels[self] := Tail(Channels[self]);

                                if(msg.type = "confirm") {
                                    tickets := tickets \ {msg.seat};
                                }
                            }
                        }
                    }   
                }
            }
        }       
    }       
               
}

*)

\* END TRANSLATION 

=============================================================================
