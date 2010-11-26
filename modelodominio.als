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

//------------------------------------------------------------------------------
// Predicados

pred passageiroEsperando[p : Passageiro, t : Time] {
    one p.esperaEm.t
}

pred passageiroEmbarcado[p : Passageiro, t : Time] {
    one p.embarcaEm.t
}

pred onibusPassaPorParada[o : Onibus, p : Parada] {
    p in o.linha.rota.paradas
}

pred onibusParadoNaParada [o : Onibus, p : Parada, t : Time] {
    onibusPassaPorParada[o, p]
    o.localizacao.t = p.localizacao
}

//------------------------------------------------------------------------------
//Estado inicial do sistema

pred init [t : Time] {
    all p: Passageiro | passageiroEsperando[p, t]
}

//------------------------------------------------------------------------------
//Trilhas

fact traces {
    init[first]

    all pre : Time - last | let pos = pre.next | some e : Event {
        e.t = pre and e.t' = pos
    }
}

//------------------------------------------------------------------------------
// Mudancas de estado

pred passageiroEmbarcaNoOnibus[p : Passageiro, o : Onibus, t, t' : Time] {
    passageiroEsperando[p, t]
    onibusParadoNaParada[o, p.esperaEm.t, t]

    p.embarcaEm.t' = o
}


pred passageiroDesembarcaNaParada[p : Passageiro, a : Parada, t, t' : Time] {
    let o = p.embarcaEm.t {
        passageiroEmbarcado[p, t]
        onibusParadoNaParada[o, a, t]
    }

    p.esperaEm.t' = a
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

//------------------------------------------------------------------------------
// Runs, asserts and checks - organizar depois

run show for 3

pred testeSemCasosTriviais[] {
    #Onibus > 2
    #Linha > 1
    #Localizacao > 3
    all r: Rota | #r.percurso > 1
    all r: Rota | #r.paradas > 1
    #Passageiro > 0
}

pred show {}

assert VerificacaoDoModelo {
    all r : Rota | all l1, l2: Linha | r in l1.rota and not l1 = l2 => not r in l2.rota

    // Nao ha rota sem linha
    all r: Rota | r in Linha.rota

    // Rota dentro de um mapa viario
    all r: Rota | some m : MapaViario | r.percurso in m.vias

    // Nao ha parada fora da rota
    all p: Parada | some r: Rota | p in r.paradas

    // Cada rota tem pelo menos uma parada
    all r : Rota | some r.paradas

    // Nao ha duas paradas na mesma localizacao
    all p1, p2 : Parada | (p1.localizacao = p2.localizacao) => (p1 = p2)

    // Ha pelo menos uma via no mapa viário
    some MapaViario.vias

    // Nao ha rota sem alguma via no percurso
    all r: Rota | some r.percurso
}

assert False {
    all t, t', t'', t''' : Time | all p : Passageiro | all a : Parada | all o : Onibus |
         passageiroEmbarcaNoOnibus[p, o, t, t'] && passageiroDesembarcaNaParada[p, a, t'', t'''] => p.esperaEm.t != a 
}

check False for 4
