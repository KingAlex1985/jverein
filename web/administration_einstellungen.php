<? include ("frame.inc"); ?>
    <h1>Administration: Einstellungen</h1>
    <h3>Allgemein</h3>
	  <p>Ab Version 2.0 werden die bisherigen Stammdaten in den allgemeinen Einstellungen gespeichert.</p>
    <img src='images/Einstellungenallgemein.png' class='screenshot'>
    <p>Der Name des Vereins und die Bankverbindung f�r die Abbuchung sind Pflichtangaben.</p>
	  <p>Eine h�ufige Anfrage ist: Warum kann ich nicht den kompletten Vereinsnamen speichern? 
	     Simpler Grund ist, dass der Vereinsname momentan nur f�r die Erzeugung von DTAUS-Dateien 
       gebraucht wird. Dort ist der Name auf 27 Stellen begrenzt.</p>

    <h3>Ansicht</h3>
    <p>Durch die Einstellungen kann das Verhalten von JVerein beeinflu�t werden.</p>
    <img src='images/Einstellungenansicht.png' class='screenshot'>
    <p class='hervorgehoben'>Nach �nderungen der mit Stern gekennzeichneten Werte ist ein Neustart 
    von Jameica erforderlich.</p>
	<p>Folgende Einstellungen k�nnen vorgenommen werden:</p>
	<ul>
	<li>Geburtsdatum und Eintrittsdatum Pflichtfeld</li>
	<li>Tab Kommunikationsdaten beim Mitglied anzeigen</li>
	<li>Tab Zusatzabbuchungen beim Mitglied anzeigen. Impliziert, dass die �bersicht der 
	Zusatzabbuchungen (nicht) angezeigt wird und die Option bei der Abbuchung (in)aktiv ist.</li>
	<li>Tab Vermerke beim Mitglied anzeigen.</li>
	<li>Tab Wiedervorlage beim Mitglied anzeigen. Impliziert, dass die �bersicht der Wiedervorlagen 
	(nicht) angezeigt wird.</li>
	<li>Kursteilnehmer ein-/ausblenden. Auswirkung auf die Abbuchung.</li>
	<li>Juristische Personen erlaubt. Die Eingabe von Firmen, Organisationen und Beh�rden als Mitglieder
		wird erlaubt. Anstatt Name und Vorname werden Name-Zeile1 und Name-Zeile2 erfasst. Geburtsdatum
		und Geschlecht werden nicht erfasst.</li>
	<li>Externe Mitgliedsnummern verwenden. Vereine, die auf Bundes- oder Landesebene organisiert 
	sind und eine durchg�ngige Mitgliedsnummer verwalten m�chten, k�nnen in JVerein eine externe 
	Mitgliedsnummer speichern.</li>
	<li>Aktuelle Geburtstage - Tage vorher/Tage nachher - Unter Jameica|Startseite anpassen|JVerein: Aktuelle Geburtstage|aktivieren
	kann die Anzeige auf der Startseite eingeschaltet werden.</li> 
	</ul>
	
	<h2><a name='beitraege'></a>Beitr�ge</h2>
    <img src='images/Einstellungenbeitraege.jpg' class='screenshot'>
	<p>Beitragsmodell, siehe auch <a href='dokumentationbeitragsmodelle.php'>Beitragsmodelle</a></</p>
	<p>Ab Version 1.3 k�nnen die Standardwerte f�r den Zahlungsweg und den Zahlungsrhytmus f�r die Neueingabe von Mitgliedern eingestellt werden.</p>
	
	<h2>Dateinamenmuster</h2>
	<img src='images/Einstellungendateinamen.jpg' class='screenshot'>
	<p>Bei der Ausgabe von Dateien (Abbuchung, Auswertungen...) werden die Dateinamen nach dem 
	vorgegebenen Muster aufgebaut. Es k�nnen zus�tzliche, vom Betriebssystem unterst�tzte Zeichen, 
	in das Muster aufgenommen werden. Bleibt das Muster leer, wird kein Vorschlag f�r den Dateinnamen 
	angezeigt. </p>
	<p>Folgende Variable stehen zur Verf�gung:</p>
	<ul>
	<li>a$ : Aufgabe (z. B. auswertung, abbuchung)</li>
	<li>d$ : Aktuelles Datum</li>
	<li>s$ : Sortierung. Wird nur bei Auswertungen gef�llt. Ansonsten leer.</li>
	<li>z$ : Aktuelle Zeit</li>
	</ul>
	
	<h2>Buchf�hrung</h2>
	<img src='images/Einstellungenbuchfuehrung.jpg' class='screenshot'>
	<p>Beginn des Gesch�ftsjahres in der Form TT.MM. </p> 

	<h2>Rechnungen</h2>
	<img src='images/Einstellungenrechnungen.jpg' class='screenshot'>
	<p>Bis Version 1.3: Festlegung, f�r welche Zahlungswege Rechnungsinformationen gespeichert werden sollen. </p>
	<p>Ab Version 1.4: Texte f�r die einzelnen Zahlungswege f�r den Rechnungsdruck. In den Text zur Abbuchung 
	k�nnen die Variablen ${Konto} und ${BLZ} eingemischt werden.</p>
	<h2><a name='tabellen'></a>Tabellen</h2>
	<p>Festlegung der Spalten, die in Tabellen angezeigt werden sollen. 
	<img src='images/Einstellungentabellen.jpg' class='screenshot'>
	

	<h2><a name=mail></a>Mail</h2>
	<img src='images/Einstellungenmail.jpg' class='screenshot'>
	<p>Alternativ zur EMail-Adresse kann auch der Name zus�tzlich im Format 
	<code>Vereinsname oder Mein Name &lt;vorstand@verein.de&gt</code>.
	Wichtig ist dabei das Format: (Name) (Spitze Klammer auf) (Email) (Spitze Klammer zu)</p>
	
	<h2><a name=statistik></a>Statistik</h2>
	<img src='images/Einstellungenstatistik.png' class='screenshot'>
		<p>F�r statistische Zwecke k�nnen Altersgruppen wie im obigen Hardcopy dargestellt angegeben 
	werden.</p>
	<p>Zur Ausgabe einer Jubil�umsliste werden die Jubeljahre durch Komma getrennt eingetragen. 
	Ohne Eingabe werden die Standardwerte 10,25,40,50 verwendet.</p>
	<p>Es kann eine Liste der Altersjubilare ausgegeben werden. Ohne Eingabe werden 
	die Standardwerte 50,60,65,70,75,80,85,90,95 verwendet.</p>
	
 <? include ("footer.inc"); ?>

