module Onibus

sig Localizacao {
}

sig Onibus {
    linha : one Linha,
    localizacao : one Localizacao
}

some sig Linha {
    onibus : some Onibus,
    rota: one Rota
}

sig Via {
    localizacoes : set Localizacao 
}

sig  Parada {
    localizacao : one Localizacao
}

sig Rota { 
    percurso : some Via,
    paradas : some Parada
}

one sig MapaViario {
    vias : some Via
}

fact NaoHaRotaSemLinha {
    all r : Rota | r in Linha.rota
}

fact UmaRotaParaCadaLinha {
    all r : Rota | one r.~rota
}

fact OnibusPertenceAUmaLinha {
   all l : Linha | all o : Onibus | o in l.onibus iff l in o.linha
}

fact NaoExisteParadaSemRota {
   all p : Parada | p in Rota.paradas
}

fact MaximoUmaParadaPorLocalizacao {
    all p1 : Parada | all p2 : Parada | p1.localizacao = p2.localizacao iff p1 = p2
}

fact ParadaEmViaDaRota {
    all l : Linha |
    l.rota.paradas.localizacao in l.rota.percurso.localizacoes
}

fact RotaEmMapaViario {
    Rota.percurso in MapaViario.vias
}

fact OnibusSempreNaRota {
   all o: Onibus | o.localizacao in o.linha.rota.percurso.localizacoes
}

fact LocalizacaoSempreEmVia {
    all l : Localizacao | l in Via.localizacoes
}

pred testeSemCasosTriviais[] {
    #Onibus > 2
    #Linha > 1
    #Localizacao > 3
    all r: Rota | #r.percurso > 1
    all r: Rota | #r.paradas > 1
}

pred show[]{

}

assert VerificacaoDoModelo {
    // Nao ha linha sem onibus
    all l : Linha | some l.onibus

    // Nao ha rota sem linha
    all r: Rota | r in Linha.rota

    // Rota dentro de um mapa viario
    all r: Rota | some m : MapaViario | r.percurso in m.vias  

    // Nao ha onibus sem linha
    all o: Onibus | some l: Linha | o in l.onibus

    // Onibus so pertence a uma linha
    all l1, l2 : Linha | all o : Onibus | (o in l1.onibus) and (o in l2.onibus) => (l1 = l2)

    // Onibus nao sai da rota
    all o : Onibus | o.localizacao in o.linha.rota.percurso.localizacoes

    // Nao ha parada fora da rota
    all p: Parada | some r: Rota | p in r.paradas

    // Cada rota tem pelo menos uma parada
    all r : Rota | some r.paradas

    // Nao ha duas paradas na mesma localizacao
    all p1, p2 : Parada | (p1.localizacao = p2.localizacao) => (p1 = p2)

    // Nao ha parada fora de via
    all p : Parada | p.localizacao in Via.localizacoes

    // Ha pelo menos uma via no mapa viário
    some MapaViario.vias

    // Nao ha rota sem alguma via no percurso
    all r: Rota | some r.percurso
}

//check VerificacaoDoModelo for 10
run testeSemCasosTriviais for 4 
