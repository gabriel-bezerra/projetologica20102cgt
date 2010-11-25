module Onibus

open util/ordering[Time]

abstract sig Time {}

// Mapa Viario
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
    localizacao : Localizacao->Time
    // capacidade maxima de passageiros
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

// Via
/*
fact TodaViaEstaEmMapaViario {
    Via in MapaViario.vias
}
*/

// Rota
/*
fact TodaRotaPossuiMaisDeUmaParada {
    all r : Rota | #r.paradas > 1
}
*/

// Linha
fact TodaRotaPertenceAUmaUnicaLinha {
    all r : Rota | one l : Linha | r in l.rota
}

/*
fact TodaLinhaPossuiPeloMenosUmOnibus {
    Linha in Onibus.linha
}
*/

// Onibus
/*
fact CapacidadeMaxima {
    all o : Onibus | #o.~embarcaEm <= 3
}
*/

// Parada
/*
fact TodaParadaEstaEmAlgumaRota {
   Parada in Rota.paradas
}
*/

fact ParadasEmLocalizacoesDiferentes {
    all p1 : Parada | all p2 : Parada | p1.localizacao = p2.localizacao iff p1 = p2
}

// Localizacao
/*
fact NaoHaLocalizacoesOrfas {
    Localizacao in (Parada.localizacao + Onibus.localizacao.Time)
}
*/

// Passageiro
fact PassageiroNoOnibusXorNaParada {
    all p : Passageiro | one p.esperaEm <=> no p.embarcaEm
    all p : Passageiro | one p.embarcaEm <=> no p.esperaEm
}

// Predicados
pred passageiroEsperando[p : Passageiro, t : Time] {
    one p.esperaEm.t
}

pred onibusPassaPorParada[o : Onibus, p : Parada] {
    p in o.linha.rota.paradas
}

pred onibusParadoNaParada [o : Onibus, p : Parada, t : Time] {
    onibusPassaPorParada[o, p]
    o.localizacao.t = p.localizacao
}

// Mudancas de estado
pred passageiroEmbarcaNoOnibus[p : Passageiro, o : Onibus, t, t' : Time] {
    passageiroEsperando[p, t]
    onibusParadoNaParada[o, p.esperaEm.t, t]

    p.embarcaEm.t' = o
}

// TODO: implementar isto
//fun mover[o : Onibus] {
//}

abstract sig Event {
}

pred init [t : Time] {
    passageiroEsperando[Passageiro, t]
}

fact traces {
    init[first]
}

run onibusParadoNaParada for 3

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

//check VerificacaoDoModelo for 10
run testeSemCasosTriviais for 4
