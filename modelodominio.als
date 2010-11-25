module Onibus

// Mapa Viario
one sig MapaViario {
    vias : some Via
}

// Via
sig Via { 
}

fact TodaViaEstaEmMapaViario {
    Via in MapaViario.vias
}

// Rota
sig Rota { 
    percurso : some Via,
    paradas : some Parada
}

fact TodaRotaPossuiMaisDeUmaParada {
    all r : Rota | #r.paradas > 1
}

fact TodaRotaPertenceAUmaUnicaLinha {
    all r : Rota | one l : Linha | r in l.rota
}

// Linha
sig Linha {
    rota: one Rota
}

fact TodaLinhaPossuiPeloMenosUmOnibus {
    Linha in Onibus.linha
}

// Onibus
sig Onibus {
    linha : one Linha,
    localizacao : one Localizacao
    // capacidade maxima de passageiros
}

fact CapacidadeMaxima {
    all o : Onibus | #o.~embarca <= 3
}

// TODO: implementar isto
//fun mover[o : Onibus] {
//}

// TODO: implementar isto
//fun parar[o : Onibus] {
//}

// Parada
sig  Parada {
    localizacao : one Localizacao
}

fact TodaParadaEstaEmAlgumaRota {
   Parada in Rota.paradas
}

fact ParadasEmLocalizacoesDiferentes {
    all p1 : Parada | all p2 : Parada | p1.localizacao = p2.localizacao iff p1 = p2
}

// Localizacao
sig Localizacao {
}

fact NaoHaLocalizacoesOrfas {
    Localizacao in (Parada.localizacao + Onibus.localizacao)
}

// Passageiro
sig Passageiro {
    esperaEm : lone Parada,
    embarca : lone Onibus
}

fact PassageiroNoOnibusXorNaParada {
    all p : Passageiro | one p.esperaEm <=> no p.embarca
    all p : Passageiro | one p.embarca <=> no p.esperaEm
}

// Predicados onibus-parada
pred onibusPassaPorParada[o : Onibus, p : Parada] {
    p in o.linha.rota.paradas
}

pred onibusParadoNaParada [o : Onibus, p : Parada] {
    onibusPassaPorParada[o, p]
    o.localizacao = p.localizacao
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

pred show[]{

}

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
