<? include ("frame.inc"); ?>
    <h1>Speicherung von Dokumenten</h1>
	<p>ab Version 2.0 verf�gbar</p>
	
	<h2>Voraussetzungen</h2>
	<p>Die Dokumentenarchivierung wird �ber den ArchiveService von Jameica realisiert. 
	Entweder erfolgt die Installation lokal oder innerhalb eines LANs. Bei der Installation
	im LAN wird in einer Jameica-Instanz der Archive-Service installiert und gestartet. 
	In den weiteren Jameica-Instanzen ist keine Installation erforderlich. Jameica findet
	die zentrale Instanz automatisch im LAN. Unter Einstellungen ist die Dokumentenspeicherung
	zu aktivieren.</p>
	
	<p>F�r den ArchiveService m�ssen folgende Jameica-Plugins zus�tzlich installiert werden:</p>
	
	<ul>
		<li>jameica.messaging</li>
		<li>jameica.soap</li>
		<li>jameica.webadmin</li>
		<li>jameica.xmlrpc</li>
	</ul>
    <p>Die Plugins stehen als Nightly-Builds unter <a href='http://www.willuhn.de/products/jameica/download_ext.php'>erweiterte Jameica-Downloads</a>
	zur Verf�gung. Zur Installation werden die Installationsdateien in das plugins-Verzeichnis von Jameica entpackt.</p>

	<h2>Allgemein</h2>
	<p>Zu Mitgliedern und Buchungen k�nnen Dokumente beliebiger Art
	und Anzahl gespeichert werden. Die Funktionalit�t steht nach der Installation der zus�tzlichen 
	Plugins ohne weitere Konfiguration zur Verf�gung.</p> 
	
    <h2>Neue Dokumente speichern</h2>
    <img src='images/dokumenteneu1.png' class='screenshot'>
    <p>Mit einem Klick auf neu �ffnet sich folgendes Formular:</p>
    <img src='images/dokumenteneu2.png' class='screenshot'>
    <p>Es wird eine Datei ausgew�hlt. Standardm�ssig wird das Tagesdatum vorgegeben.
    Es kann hier z. B. auch das Datum des Beleges eingetragen werden. Zus�tzlich kann
    zu jedem Dokument ein Kommentar eingetragen werden.</p>
 
    <h2>Dokumente anzeigen oder l�schen</h2>
    <p>Mit einem Rechtsklick auf ein Dokument �ffnet sich ein Kontextmen�. Mit den Men�punkten
    kann ein Dokument entweder angezeigt oder gel�scht werden.</p>
    
    <h2>Datensicherung</h2>
    <p>Die gespeicherten Dokumente werden nicht durch die Sicherung von Jameica erfasst. Am einfachsten
    ist es, dass .jameica-Verzeichns komplett zu sichern.</p> 
    
<? include ("footer.inc"); ?>

