module Onibus

open util/ordering[Time]

abstract sig Time {}

//------------------------------------------------------------------------------
// Entidades do dominio

one sig MapaViario {
    vias : some Via
}

sig Via {
}

sig Rota {
    percurso : some Via,
    paradas : some Parada
}

sig Linha {
    rota: one Rota
}

sig Onibus {
    linha : one Linha,
    localizacao : Localizacao one->Time
}

sig  Parada {
    localizacao : one Localizacao
}

sig Localizacao {
}

sig Passageiro {
    esperaEm : Parada lone-> Time,
    embarcaEm : Onibus lone-> Time
}

//------------------------------------------------------------------------------
// Fatos

fact TodaViaEstaEmMapaViario {
    Via in MapaViario.vias
}

fact TodaRotaPossuiMaisDeUmaParada {
    all r : Rota | #r.paradas > 1
}

fact TodaRotaPertenceAUmaUnicaLinha {
    all r : Rota | one l : Linha | r in l.rota
}

fact TodaLinhaPossuiPeloMenosUmOnibus {
    Linha in Onibus.linha
}

fact TodaParadaEstaEmAlgumaRota {
   Parada in Rota.paradas
}

fact ParadasEmLocalizacoesDiferentes {
    all p1 : Parada | all p2 : Parada {
        p1.localizacao = p2.localizacao iff p1 = p2
    }
}

fact NaoHaLocalizacoesOrfas {
    Localizacao in (Parada.localizacao + Onibus.localizacao.Time)
}

fact PassageiroNoOnibusXorNaParada {
    all t : Time {
        all p : Passageiro | one p.esperaEm.t <=> no p.embarcaEm.t
        all p : Passageiro | one p.embarcaEm.t <=> no p.esperaEm.t
    }
}

fact PassageiroNaoEmbarcaForaDaParada {
    all t, t': Time | all p: Passageiro | all a: Parada | all o: Onibus {
        passageiroEsperandoNaParada[p, a, t] and not onibusParadoNaParada[o, a, t]
            => not passageiroEmbarcadoNoOnibus[p, o, t']
    }
}

//------------------------------------------------------------------------------
// Predicados

pred passageiroEsperando[p : Passageiro, t : Time] {
    one p.esperaEm.t
}

pred passageiroEmbarcado[p : Passageiro, t : Time] {
    one p.embarcaEm.t
}

pred passageiroEsperandoNaParada[p: Passageiro, a: Parada, t : Time] {
    p.esperaEm.t = a
}

pred passageiroEmbarcadoNoOnibus[p: Passageiro, o: Onibus, t : Time] {
    p.embarcaEm.t = o
}

pred onibusPassaPorParada[o : Onibus, p : Parada] {
    p in o.linha.rota.paradas
}

pred onibusEstaNaParada[o: Onibus, p: Parada, t: Time] {
    o.localizacao.t = p.localizacao
}

pred onibusParadoNaParada [o : Onibus, p : Parada, t : Time] {
    onibusPassaPorParada[o, p]
    onibusEstaNaParada[o, p, t]
}

//------------------------------------------------------------------------------
//Estados inicial e final do sistema

pred init [t : Time] {
    all p: Passageiro | passageiroEsperando[p, t]
}

pred finish [t : Time] {
    all p: Passageiro | passageiroEsperando[p, t]
}

//------------------------------------------------------------------------------
//Trilhas

fact traces {
    init[first]
    finish[last]

    all pre : Time - last | let pos = pre.next | some e : Event {
        e.t = pre and e.t' = pos
    }
}

//------------------------------------------------------------------------------
// Mudancas de estado

pred passageiroEmbarcaNoOnibus[p : Passageiro, o : Onibus, t, t' : Time] {
    some a: Parada {
        passageiroEsperandoNaParada[p, a, t]
        onibusParadoNaParada[o, a, t]
    }

    passageiroEmbarcadoNoOnibus[p, o, t']
}

pred passageiroDesembarcaNaParada[p : Passageiro, a : Parada, t, t' : Time] {
    some o: Onibus {
        passageiroEmbarcadoNoOnibus[p, o, t]
        onibusParadoNaParada[o, a, t]
    }

    passageiroEsperandoNaParada[p, a, t']
}

pred onibusMove[o: Onibus, l: Localizacao, t, t': Time] {
    not o.localizacao.t = l

    o.localizacao.t' = l
}

//------------------------------------------------------------------------------
// Eventos

abstract sig Event {
    t, t' : Time
}

abstract sig EmbarqueEvent extends Event {
    p : Passageiro,
    o : Onibus
} {
    passageiroEmbarcaNoOnibus[p, o, t, t']
}

abstract sig DesembarqueEvent extends Event {
    p : Passageiro,
    a : Parada
} {
    passageiroDesembarcaNaParada[p, a, t, t']
}

abstract sig OnibusMoveEvent extends Event {
    o : Onibus,
    l : Localizacao
} {
    onibusMove[o, l, t, t']
}

//------------------------------------------------------------------------------
// Run

pred show {}
run show for 3

pred testeSemCasosTriviais[] {
    #Onibus > 2
    #Linha > 1
    #Localizacao > 3
    all r: Rota | #r.percurso > 1
    #Passageiro > 0
}
run testeSemCasosTriviais for 4

//------------------------------------------------------------------------------
// Check

// verifica a correção dos predicados sobre passageiro embarcado
assert CorrecaoEmbarcados {
    all p: Passageiro | all t: Time {
        passageiroEmbarcado[p, t]
            => some o: Onibus | passageiroEmbarcadoNoOnibus[p, o, t]
    }
}
check CorrecaoEmbarcados for 10

// verifica a correção dos predicados sobre passageiro esperando
assert CorrecaoEsperandos {
    all p: Passageiro | all t: Time {
        passageiroEsperando[p, t]
            => some a: Parada | passageiroEsperandoNaParada[p, a, t]
    }
}
check CorrecaoEsperandos for 10

assert PassageiroEmbarcadoDeveDesembarcarEmAlgumMomento {
    all p: Passageiro | all t: Time {
        passageiroEmbarcado[p, t] =>
            (some t': Time | t' in t.^next and passageiroEsperando[p, t'])
    }
}
check PassageiroEmbarcadoDeveDesembarcarEmAlgumMomento for 10

assert TodoOnibusPassaPorAlgumaParada {
    all o: Onibus | some a : Parada | onibusPassaPorParada[o, a]
}
check  TodoOnibusPassaPorAlgumaParada for 10
